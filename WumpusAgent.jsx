import { useState, useEffect, useCallback, useRef } from "react";

// ─────────────────────────────────────────────
//  PROPOSITIONAL LOGIC & RESOLUTION ENGINE
// ─────────────────────────────────────────────

function toCNFClauses(r, c, percepts, rows, cols) {
  const clauses = [];
  const adj = getAdj(r, c, rows, cols);

  if (percepts.breeze) {
    // B_r,c <=> OR(P_adj)  →  split into two implications
    // forward: ¬B ∨ P_a1 ∨ P_a2 ...  (B ⇒ disjunction) — not needed for resolution
    // backward: for each adj a: ¬P_a ∨ B  → already in KB as fact B
    // We add: if B then at least one adjacent pit
    const pitLiterals = adj.map(([ar, ac]) => `P_${ar}_${ac}`);
    clauses.push(pitLiterals); // at least one adj pit
  } else {
    // No breeze → no pits adjacent
    adj.forEach(([ar, ac]) => clauses.push([`¬P_${ar}_${ac}`]));
  }

  if (percepts.stench) {
    const wLiterals = adj.map(([ar, ac]) => `W_${ar}_${ac}`);
    clauses.push(wLiterals);
  } else {
    adj.forEach(([ar, ac]) => clauses.push([`¬W_${ar}_${ac}`]));
  }

  return clauses;
}

function getAdj(r, c, rows, cols) {
  const dirs = [[-1,0],[1,0],[0,-1],[0,1]];
  return dirs
    .map(([dr, dc]) => [r+dr, c+dc])
    .filter(([nr, nc]) => nr>=0 && nr<rows && nc>=0 && nc<cols);
}

// Resolution refutation: prove literal is true by assuming ¬literal and deriving ⊥
function resolutionRefute(kb, literal) {
  // Add negation of goal
  const negLit = literal.startsWith("¬") ? literal.slice(1) : `¬${literal}`;
  const clauses = kb.map(c => [...c]);
  clauses.push([negLit]);

  let steps = 0;
  const maxSteps = 500;

  // Convert to set of frozensets for dedup
  const clauseSet = new Set(clauses.map(c => canonicalize(c)));
  const clauseList = clauses.map(c => [...c]);

  while (steps < maxSteps) {
    let newClauses = [];
    const list = [...clauseList];

    for (let i = 0; i < list.length; i++) {
      for (let j = i+1; j < list.length; j++) {
        const resolvents = resolve(list[i], list[j]);
        for (const r of resolvents) {
          if (r.length === 0) return { proved: true, steps };
          const key = canonicalize(r);
          if (!clauseSet.has(key)) {
            newClauses.push(r);
            clauseSet.add(key);
            clauseList.push(r);
          }
        }
        steps++;
        if (steps > maxSteps) return { proved: false, steps };
      }
    }

    if (newClauses.length === 0) return { proved: false, steps };
  }
  return { proved: false, steps };
}

function canonicalize(clause) {
  return [...clause].sort().join("|");
}

function resolve(c1, c2) {
  const results = [];
  for (const lit of c1) {
    const neg = lit.startsWith("¬") ? lit.slice(1) : `¬${lit}`;
    if (c2.includes(neg)) {
      const resolvent = [
        ...c1.filter(l => l !== lit),
        ...c2.filter(l => l !== neg)
      ];
      // Remove tautologies
      const isTaut = resolvent.some(l => {
        const nl = l.startsWith("¬") ? l.slice(1) : `¬${l}`;
        return resolvent.includes(nl);
      });
      if (!isTaut) results.push([...new Set(resolvent)]);
    }
  }
  return results;
}

// ─────────────────────────────────────────────
//  GAME LOGIC
// ─────────────────────────────────────────────

function initGrid(rows, cols) {
  const grid = Array.from({ length: rows }, () =>
    Array.from({ length: cols }, () => ({
      pit: false, wumpus: false, gold: false,
      visited: false, safe: false, inferred: "unknown",
      breeze: false, stench: false, glitter: false
    }))
  );

  // Place hazards randomly (not at start [rows-1][0])
  const cells = [];
  for (let r = 0; r < rows; r++)
    for (let c = 0; c < cols; c++)
      if (!(r === rows-1 && c === 0)) cells.push([r, c]);

  // Shuffle
  for (let i = cells.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i+1));
    [cells[i], cells[j]] = [cells[j], cells[i]];
  }

  // ~20% pits
  const numPits = Math.max(1, Math.floor(rows * cols * 0.18));
  for (let i = 0; i < numPits && i < cells.length; i++) {
    const [r, c] = cells[i];
    grid[r][c].pit = true;
  }

  // 1 wumpus
  if (cells.length > numPits) {
    const [wr, wc] = cells[numPits];
    grid[wr][wc].wumpus = true;
  }

  // 1 gold
  if (cells.length > numPits + 1) {
    const [gr, gc] = cells[numPits + 1];
    grid[gr][gc].gold = true;
  }

  // Generate percepts
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const adj = getAdj(r, c, rows, cols);
      grid[r][c].breeze = adj.some(([ar, ac]) => grid[ar][ac].pit);
      grid[r][c].stench = adj.some(([ar, ac]) => grid[ar][ac].wumpus);
    }
  }

  return grid;
}

// ─────────────────────────────────────────────
//  MAIN COMPONENT
// ─────────────────────────────────────────────

export default function WumpusAgent() {
  const [rows, setRows] = useState(4);
  const [cols, setCols] = useState(4);
  const [grid, setGrid] = useState(null);
  const [agentPos, setAgentPos] = useState([3, 0]);
  const [kb, setKb] = useState([]);
  const [log, setLog] = useState([]);
  const [inferenceSteps, setInferenceSteps] = useState(0);
  const [gameOver, setGameOver] = useState(null); // null | 'dead' | 'gold' | 'escaped'
  const [showHazards, setShowHazards] = useState(false);
  const [cellStatus, setCellStatus] = useState({});
  const logRef = useRef(null);

  const addLog = useCallback((msg) => {
    setLog(prev => [...prev.slice(-60), msg]);
  }, []);

  useEffect(() => {
    if (logRef.current) logRef.current.scrollTop = logRef.current.scrollHeight;
  }, [log]);

  const startGame = useCallback(() => {
    const g = initGrid(rows, cols);
    const startR = rows - 1, startC = 0;
    g[startR][startC].visited = true;
    g[startR][startC].safe = true;

    const initialKb = [[`¬P_${startR}_${startC}`], [`¬W_${startR}_${startC}`]];
    const percepts = { breeze: g[startR][startC].breeze, stench: g[startR][startC].stench };
    const newClauses = toCNFClauses(startR, startC, percepts, rows, cols);
    const fullKb = [...initialKb, ...newClauses];

    setGrid(g);
    setAgentPos([startR, startC]);
    setKb(fullKb);
    setLog([]);
    setInferenceSteps(0);
    setGameOver(null);
    setShowHazards(false);
    setCellStatus({});
    addLog(`▶ Game started. Agent at [${startR},${startC}].`);
    if (percepts.breeze) addLog("💨 Breeze detected!");
    if (percepts.stench) addLog("💀 Stench detected!");
    if (g[startR][startC].glitter) addLog("✨ Glitter! Gold is here!");
  }, [rows, cols, addLog]);

  useEffect(() => { startGame(); }, []);

  const moveAgent = useCallback((nr, nc) => {
    if (!grid || gameOver) return;
    const cell = grid[nr][nc];

    // Check safety via resolution before moving
    const safePit = resolutionRefute(kb, `¬P_${nr}_${nc}`);
    const safeWumpus = resolutionRefute(kb, `¬W_${nr}_${nc}`);
    const totalSteps = safePit.steps + safeWumpus.steps;
    setInferenceSteps(prev => prev + totalSteps);

    const inferredSafe = safePit.proved && safeWumpus.proved;

    addLog(`→ Moving to [${nr},${nc}] — ${inferredSafe ? "✅ Proved safe" : "⚠️ Safety unproven"} (${totalSteps} steps)`);

    const newGrid = grid.map(row => row.map(cell => ({ ...cell })));
    newGrid[nr][nc].visited = true;
    if (inferredSafe) newGrid[nr][nc].safe = true;

    // Update KB with new percepts
    const percepts = { breeze: cell.breeze, stench: cell.stench };
    const newClauses = toCNFClauses(nr, nc, percepts, rows, cols);
    const newKb = [...kb, [`¬P_${nr}_${nc}`], [`¬W_${nr}_${nc}`], ...newClauses];

    setGrid(newGrid);
    setAgentPos([nr, nc]);
    setKb(newKb);

    if (percepts.breeze) addLog("💨 Breeze detected!");
    if (percepts.stench) addLog("💀 Stench detected!");
    if (cell.gold) addLog("🏆 GOLD FOUND!");

    // Update cell status display
    const newStatus = { ...cellStatus };
    newStatus[`${nr}_${nc}`] = inferredSafe ? "safe" : "unknown";
    setCellStatus(newStatus);

    // Check game events
    if (cell.pit) {
      addLog("💥 Fell into a pit! GAME OVER.");
      setGameOver("dead");
      setShowHazards(true);
    } else if (cell.wumpus) {
      addLog("🐉 Eaten by the Wumpus! GAME OVER.");
      setGameOver("dead");
      setShowHazards(true);
    } else if (cell.gold) {
      setGameOver("gold");
      setShowHazards(true);
    }
  }, [grid, gameOver, kb, rows, cols, addLog, cellStatus]);

  const getAdjacentMoves = useCallback(() => {
    if (!agentPos || !grid) return [];
    const [r, c] = agentPos;
    return getAdj(r, c, rows, cols).filter(([nr, nc]) => !grid[nr][nc].visited || true);
  }, [agentPos, grid, rows, cols]);

  const getCellColor = (r, c) => {
    if (!grid) return "#1a1a2e";
    const cell = grid[r][c];
    const isAgent = agentPos[0] === r && agentPos[1] === c;
    if (isAgent) return "#f0c040";
    if (showHazards && cell.pit) return "#e74c3c";
    if (showHazards && cell.wumpus) return "#c0392b";
    if (showHazards && cell.gold && !gameOver?.includes("dead")) return "#f1c40f";
    if (!cell.visited) return "#0d1b2a";
    if (cell.safe) return "#1a472a";
    return "#2c3e50";
  };

  const getCellIcon = (r, c) => {
    if (!grid) return "";
    const cell = grid[r][c];
    const isAgent = agentPos[0] === r && agentPos[1] === c;
    const adj = getAdjacentMoves().some(([nr, nc]) => nr === r && nc === c);
    if (isAgent) return "🤖";
    if (showHazards && cell.pit) return "🕳️";
    if (showHazards && cell.wumpus) return "🐉";
    if (showHazards && cell.gold) return "💰";
    if (!cell.visited && adj) return "❓";
    if (!cell.visited) return "";
    if (cell.breeze && cell.stench) return "💨💀";
    if (cell.breeze) return "💨";
    if (cell.stench) return "💀";
    if (cell.safe) return "✓";
    return "";
  };

  return (
    <div style={{
      fontFamily: "'Courier New', monospace",
      background: "#0a0a14",
      minHeight: "100vh",
      color: "#e0e0ff",
      padding: "16px",
      boxSizing: "border-box"
    }}>
      <div style={{ textAlign: "center", marginBottom: 12 }}>
        <div style={{
          fontSize: 22, fontWeight: "bold", letterSpacing: 3,
          color: "#7ec8e3", textTransform: "uppercase"
        }}>
          ⚡ Wumpus Logic Agent
        </div>
        <div style={{ fontSize: 11, color: "#556", marginTop: 2 }}>
          Propositional Resolution Inference Engine
        </div>
      </div>

      {/* Config */}
      <div style={{
        display: "flex", gap: 8, flexWrap: "wrap",
        justifyContent: "center", marginBottom: 12, alignItems: "center"
      }}>
        {[["Rows", rows, setRows], ["Cols", cols, setCols]].map(([label, val, setter]) => (
          <label key={label} style={{ fontSize: 12, color: "#aaa" }}>
            {label}:
            <select
              value={val}
              onChange={e => setter(Number(e.target.value))}
              style={{
                marginLeft: 4, background: "#1a1a2e", color: "#7ec8e3",
                border: "1px solid #334", padding: "2px 6px", borderRadius: 4,
                cursor: "pointer"
              }}
            >
              {[3,4,5,6].map(n => <option key={n} value={n}>{n}</option>)}
            </select>
          </label>
        ))}
        <button onClick={startGame} style={btnStyle("#7ec8e3", "#0a0a14")}>
          ▶ New Game
        </button>
        <button onClick={() => setShowHazards(s => !s)} style={btnStyle("#e8a838", "#0a0a14")}>
          {showHazards ? "🙈 Hide" : "👁 Reveal"} Map
        </button>
      </div>

      {/* Metrics */}
      <div style={{
        display: "flex", gap: 12, justifyContent: "center",
        marginBottom: 12, flexWrap: "wrap"
      }}>
        {[
          ["KB Clauses", kb.length],
          ["Inference Steps", inferenceSteps],
          ["Agent Pos", agentPos ? `[${agentPos[0]},${agentPos[1]}]` : "-"],
          ["Status", gameOver ? gameOver.toUpperCase() : "EXPLORING"]
        ].map(([label, val]) => (
          <div key={label} style={{
            background: "#111122", border: "1px solid #223",
            borderRadius: 6, padding: "4px 12px", textAlign: "center"
          }}>
            <div style={{ fontSize: 9, color: "#556", textTransform: "uppercase" }}>{label}</div>
            <div style={{ fontSize: 14, color: "#7ec8e3", fontWeight: "bold" }}>{val}</div>
          </div>
        ))}
      </div>

      {/* Game Over Banner */}
      {gameOver && (
        <div style={{
          textAlign: "center", padding: "8px",
          background: gameOver === "gold" ? "#1a3a1a" : "#3a1a1a",
          border: `1px solid ${gameOver === "gold" ? "#2ecc71" : "#e74c3c"}`,
          borderRadius: 6, marginBottom: 10, fontSize: 14, fontWeight: "bold",
          color: gameOver === "gold" ? "#2ecc71" : "#e74c3c"
        }}>
          {gameOver === "gold" ? "🏆 GOLD RETRIEVED! VICTORY!" : "💥 AGENT DESTROYED! GAME OVER"}
        </div>
      )}

      <div style={{ display: "flex", gap: 12, flexWrap: "wrap", justifyContent: "center" }}>
        {/* Grid */}
        <div>
          <div style={{
            display: "grid",
            gridTemplateColumns: `repeat(${cols}, 1fr)`,
            gap: 3,
            marginBottom: 8
          }}>
            {grid && Array.from({ length: rows }, (_, r) =>
              Array.from({ length: cols }, (_, c) => {
                const isAdj = !gameOver && getAdjacentMoves().some(([nr, nc]) => nr === r && nc === c);
                const isAgent = agentPos[0] === r && agentPos[1] === c;
                return (
                  <div
                    key={`${r}-${c}`}
                    onClick={() => isAdj && !gameOver && moveAgent(r, c)}
                    style={{
                      width: 58, height: 58,
                      background: getCellColor(r, c),
                      border: isAgent
                        ? "2px solid #f0c040"
                        : isAdj
                          ? "2px dashed #7ec8e3"
                          : "1px solid #223",
                      borderRadius: 4,
                      display: "flex", flexDirection: "column",
                      alignItems: "center", justifyContent: "center",
                      cursor: isAdj && !gameOver ? "pointer" : "default",
                      fontSize: 18,
                      transition: "all 0.15s",
                      position: "relative",
                      boxShadow: isAdj ? "0 0 8px #7ec8e344" : "none"
                    }}
                  >
                    <span>{getCellIcon(r, c)}</span>
                    <span style={{ fontSize: 8, color: "#445", position: "absolute", bottom: 2, right: 4 }}>
                      {r},{c}
                    </span>
                  </div>
                );
              })
            )}
          </div>

          {/* Legend */}
          <div style={{ display: "flex", gap: 8, flexWrap: "wrap", fontSize: 10, color: "#556" }}>
            {[
              ["🤖", "Agent"], ["✓", "Safe"], ["❓", "Clickable"],
              ["💨", "Breeze"], ["💀", "Stench"],
              ["🕳️", "Pit"], ["🐉", "Wumpus"], ["💰", "Gold"]
            ].map(([icon, label]) => (
              <span key={label}>{icon} {label}</span>
            ))}
          </div>
        </div>

        {/* Log Panel */}
        <div style={{
          background: "#050510", border: "1px solid #223",
          borderRadius: 6, padding: 8, width: 240,
          display: "flex", flexDirection: "column"
        }}>
          <div style={{ fontSize: 10, color: "#445", textTransform: "uppercase", marginBottom: 6 }}>
            Inference Log
          </div>
          <div
            ref={logRef}
            style={{
              overflowY: "auto", flex: 1,
              maxHeight: 280, fontSize: 11, lineHeight: 1.6,
              color: "#8899aa"
            }}
          >
            {log.map((l, i) => (
              <div key={i} style={{
                padding: "1px 0",
                color: l.startsWith("→") ? "#7ec8e3"
                  : l.includes("GAME OVER") || l.includes("GOLD") ? "#f0c040"
                  : l.includes("Proved safe") ? "#2ecc71"
                  : l.includes("unproven") ? "#e67e22"
                  : "#8899aa"
              }}>
                {l}
              </div>
            ))}
          </div>
        </div>
      </div>

      {/* Current Percepts */}
      {grid && agentPos && !gameOver && (
        <div style={{
          marginTop: 10, textAlign: "center",
          fontSize: 12, color: "#7ec8e3"
        }}>
          Current percepts at [{agentPos[0]},{agentPos[1]}]:&nbsp;
          <strong>
            {[
              grid[agentPos[0]][agentPos[1]].breeze && "BREEZE",
              grid[agentPos[0]][agentPos[1]].stench && "STENCH",
              grid[agentPos[0]][agentPos[1]].gold && "GLITTER"
            ].filter(Boolean).join(", ") || "NONE"}
          </strong>
        </div>
      )}

      <div style={{ marginTop: 12, textAlign: "center", fontSize: 10, color: "#334" }}>
        Click dashed cells (❓) to move. Agent uses Resolution Refutation to infer cell safety before each move.
      </div>
    </div>
  );
}

function btnStyle(color, bg) {
  return {
    background: "transparent",
    border: `1px solid ${color}`,
    color: color,
    padding: "4px 14px",
    borderRadius: 4,
    cursor: "pointer",
    fontSize: 12,
    fontFamily: "'Courier New', monospace"
  };
}
