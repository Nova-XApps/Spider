const { useState, useMemo, useEffect } = React;

// ═══════════════════════════════════════════════════════════════════════════
// SCHEDULING ENGINE v3 — Min-Cost Flow (SPFA / Successive Shortest Paths)
// ═══════════════════════════════════════════════════════════════════════════

// ── Constants ──────────────────────────────────────────────────────────────
const QUANT             = 2;    // integer units per hour (0.5 h steps)
const MAX_SESSION_UNITS = 6;    // 3 h max per task per slot
const MIN_SESSION_UNITS = 1;    // 0.5 h minimum (unused, kept for completeness)

const URGENCY_SCALE = 10;
const WEIGHT_SCALE  = 20;
const DIFF_SCALE    = 5;
const MAX_WEIGHT    = 5;

// ── Graph helpers ──────────────────────────────────────────────────────────
function makeEdge(graph, u, v, cap, cost) {
  graph[u].push({ to: v, cap, cost, flow: 0, rev: graph[v].length });
  graph[v].push({ to: u, cap: 0, cost: -cost, flow: 0, rev: graph[u].length - 1 });
}

function spfa(graph, source, sink, n) {
  const INF  = 2 ** 30;
  const dist = new Int32Array(n).fill(INF);
  const inQ  = new Uint8Array(n);
  const prevNode = new Int32Array(n).fill(-1);
  const prevEdge = new Int32Array(n).fill(-1);

  dist[source] = 0;
  const queue = [source];
  inQ[source] = 1;

  let head = 0;
  while (head < queue.length) {
    const u = queue[head++];
    inQ[u] = 0;

    for (let i = 0; i < graph[u].length; i++) {
      const e = graph[u][i];
      if (e.cap - e.flow > 0 && dist[u] + e.cost < dist[e.to]) {
        dist[e.to] = dist[u] + e.cost;
        prevNode[e.to] = u;
        prevEdge[e.to] = i;
        if (!inQ[e.to]) {
          queue.push(e.to);
          inQ[e.to] = 1;
        }
      }
    }
  }

  if (dist[sink] === INF) return null;
  return { dist, prevNode, prevEdge };
}

function augment(graph, sink, prevNode, prevEdge) {
  let u = sink;
  let bottleneck = 2 ** 30;
  while (prevNode[u] !== -1) {
    const e = graph[prevNode[u]][prevEdge[u]];
    bottleneck = Math.min(bottleneck, e.cap - e.flow);
    u = prevNode[u];
  }
  u = sink;
  while (prevNode[u] !== -1) {
    const e  = graph[prevNode[u]][prevEdge[u]];
    e.flow  += bottleneck;
    graph[e.to][e.rev].flow -= bottleneck;
    u = prevNode[u];
  }
  return bottleneck;
}

function edgeCost(task, slotDate) {
  const taskDueMs  = new Date(task.dueDate + "T00:00:00").getTime();
  const slotDateMs = new Date(slotDate    + "T00:00:00").getTime();
  const daysOfSlack = Math.max(0, Math.round((taskDueMs - slotDateMs) / 86_400_000));

  const urgencyPenalty  = daysOfSlack * URGENCY_SCALE;
  const importanceSaving = (MAX_WEIGHT - task.weight) * WEIGHT_SCALE;
  const difficultyBonus  = (task.difficulty ?? 2) * DIFF_SCALE;

  return Math.max(0, urgencyPenalty + importanceSaving - difficultyBonus);
}

function scorePriority({ daysUntilDue, estimatedHours, weight, difficulty }) {
  const urgency    = daysUntilDue === 0 ? 20
                   : daysUntilDue <= 2  ? 10 + (2 - daysUntilDue) * 5
                   : Math.max(0, 10 - daysUntilDue * 0.8);
  const impact     = weight * 2;
  const load       = (difficulty ?? 2) * 1.2;
  const timeStress = estimatedHours > 4 ? 2 : 0;
  return Math.round(urgency + impact + load + timeStress);
}

// ── Main scheduler ──────────────────────────────────────────────────────────
function generateSchedule(rawTasks, availableSlots) {
  if (!rawTasks.length || !availableSlots.length) return { schedule: [], infeasible: [] };

  const slots = [...availableSlots].sort((a, b) => a.date.localeCompare(b.date));
  const slotHoursQ = slots.map(s => Math.round(s.hours * QUANT));

  const prefixCap = new Int32Array(slots.length);
  prefixCap[0] = slotHoursQ[0];
  for (let j = 1; j < slots.length; j++) prefixCap[j] = prefixCap[j - 1] + slotHoursQ[j];

  function lastSlotBeforeDeadline(dueDate) {
    let lo = 0, hi = slots.length - 1, result = -1;
    while (lo <= hi) {
      const mid = (lo + hi) >>> 1;
      if (slots[mid].date <= dueDate) { result = mid; lo = mid + 1; }
      else hi = mid - 1;
    }
    return result;
  }

  const tasks = rawTasks.map(t => {
    const deadlineSlotIdx = lastSlotBeforeDeadline(t.dueDate);
    const capacityQ = deadlineSlotIdx >= 0 ? prefixCap[deadlineSlotIdx] : 0;
    const demandQ   = Math.round((t.estimatedHours ?? 0) * QUANT);
    const feasibleQ = deadlineSlotIdx < 0 ? 0 : Math.min(demandQ, capacityQ);
    const shortfallH = (demandQ - feasibleQ) / QUANT;
    return {
      ...t,
      demandQ,
      feasibleQ,
      shortfallH,
      deadlineSlotIdx,
      infeasible: feasibleQ < demandQ,
    };
  });

  // ── Build flow graph ──────────────────────────────────────────────────────
  const T = tasks.length;
  const S = slots.length;
  const SOURCE = 0;
  const SINK   = T + S + 1;
  const N      = T + S + 2;

  const taskNode = i => 1 + i;
  const slotNode = j => 1 + T + j;

  const graph = Array.from({ length: N }, () => []);

  for (let i = 0; i < T; i++) {
    if (tasks[i].feasibleQ > 0) {
      makeEdge(graph, SOURCE, taskNode(i), tasks[i].feasibleQ, 0);
    }
  }

  for (let i = 0; i < T; i++) {
    if (tasks[i].feasibleQ === 0) continue;
    for (let j = 0; j <= tasks[i].deadlineSlotIdx; j++) {
      const cap  = Math.min(MAX_SESSION_UNITS, slotHoursQ[j]);
      const cost = edgeCost(tasks[i], slots[j].date);
      makeEdge(graph, taskNode(i), slotNode(j), cap, cost);
    }
  }

  for (let j = 0; j < S; j++) {
    makeEdge(graph, slotNode(j), SINK, slotHoursQ[j], 0);
  }

  // ── Run MCF ───────────────────────────────────────────────────────────────
  let totalFlow = 0;
  for (;;) {
    const res = spfa(graph, SOURCE, SINK, N);
    if (!res) break;
    totalFlow += augment(graph, SINK, res.prevNode, res.prevEdge);
  }

  // ── Read flows ────────────────────────────────────────────────────────────
  const sessionMap = Array.from({ length: S }, () => new Map());
  const taskFlow = new Int32Array(T).fill(0); // actual scheduled units per task

  for (let i = 0; i < T; i++) {
    const tn = taskNode(i);
    for (const edge of graph[tn]) {
      if (edge.flow <= 0 || edge.cost < 0) continue;
      const j = edge.to - (1 + T);
      if (j < 0 || j >= S) continue;
      sessionMap[j].set(tasks[i].id, (sessionMap[j].get(tasks[i].id) ?? 0) + edge.flow);
      taskFlow[i] += edge.flow;
    }
  }

  // ── Build schedule & infeasible list ──────────────────────────────────────
  const displayPriority = new Map();
  tasks.forEach(t => {
    const slotMs = new Date(slots[0].date + "T00:00:00").getTime();
    const dueMs  = new Date(t.dueDate     + "T00:00:00").getTime();
    const daysUntilDue = Math.max(0, Math.round((dueMs - slotMs) / 86_400_000));
    displayPriority.set(t.id, scorePriority({ ...t, daysUntilDue }));
  });

  const taskById = new Map(tasks.map(t => [t.id, t]));
  const schedule = [];
  for (let j = 0; j < S; j++) {
    if (sessionMap[j].size === 0) continue;
    const sessions = [];
    for (const [taskId, units] of sessionMap[j]) {
      const hours = units / QUANT;
      const t = taskById.get(taskId);
      sessions.push({
        taskId,
        taskName : t.name,
        subject  : t.subject,
        hours,
        priority : displayPriority.get(taskId) ?? 0,
      });
    }
    sessions.sort((a, b) => b.priority - a.priority);
    schedule.push({ date: slots[j].date, sessions });
  }

  // Infeasibility report
  const infeasible = tasks
    .filter((t, i) => t.infeasible || taskFlow[i] < t.demandQ)
    .map((t, i) => {
      const actualShortfall = (t.demandQ - taskFlow[i]) / QUANT;
      return {
        id: t.id,
        name: t.name,
        requested: t.demandQ / QUANT,
        scheduled: taskFlow[i] / QUANT,
        shortfall: actualShortfall,
        reason: taskFlow[i] < t.demandQ ? "Insufficient capacity before deadline" : "Pre‑flow capping",
      };
    });

  return { schedule, infeasible };
}

// ─── LOCAL STORAGE HELPERS ────────────────────────────────────────────────
const STORAGE_KEY_TASKS = 'studyos_tasks';
const STORAGE_KEY_SLOTS = 'studyos_slots';

function loadFromStorage(key, fallback) {
  try {
    const stored = localStorage.getItem(key);
    return stored ? JSON.parse(stored) : fallback;
  } catch {
    return fallback;
  }
}

function saveToStorage(key, data) {
  try {
    localStorage.setItem(key, JSON.stringify(data));
  } catch {}
}

// ─── UI CONSTANTS ─────────────────────────────────────────────────────────
const SUBJECTS = ["Math", "Science", "English", "History", "CS", "Art", "Language", "Other"];
const DIFFICULTIES = [{ v: 1, l: "Easy" }, { v: 2, l: "Medium" }, { v: 3, l: "Hard" }, { v: 4, l: "Very Hard" }];
const TASK_TYPES = ["Assignment", "Test Prep", "Project", "Reading", "Lab", "Essay"];
const COLORS = {
  Math: "#f59e0b", Science: "#10b981", English: "#6366f1", History: "#ef4444",
  CS: "#3b82f6", Art: "#ec4899", Language: "#8b5cf6", Other: "#64748b",
};

function today() {
  return new Date().toISOString().split("T")[0];
}
function daysFrom(dateStr) {
  const d = new Date(dateStr + "T00:00:00");
  const now = new Date();
  now.setHours(0, 0, 0, 0);
  return Math.max(0, Math.round((d - now) / 86400000));
}
function fmtDate(dateStr) {
  return new Date(dateStr + "T00:00:00").toLocaleDateString("en-US", { weekday: "short", month: "short", day: "numeric" });
}

// ─── COMPONENTS ──────────────────────────────────────────────────────────
function Badge({ color, children }) {
  return React.createElement('span', {
    style: {
      background: color + "22", color, border: `1px solid ${color}44`,
      borderRadius: 6, padding: "2px 8px", fontSize: 11, fontWeight: 700,
      letterSpacing: 0.5, display: 'inline-block'
    }
  }, children);
}

function PriorityBar({ score }) {
  const max = 40;
  const pct = Math.min(100, (score / max) * 100);
  const color = pct > 70 ? "#ef4444" : pct > 40 ? "#f59e0b" : "#10b981";
  return React.createElement('div', { style: { display: 'flex', alignItems: 'center', gap: 6 } },
    React.createElement('div', { style: { flex: 1, height: 5, background: '#1e293b', borderRadius: 4, overflow: 'hidden' } },
      React.createElement('div', { style: { width: `${pct}%`, height: '100%', background: color, borderRadius: 4, transition: 'width 0.4s ease' } })
    ),
    React.createElement('span', { style: { fontSize: 11, color, fontWeight: 700, minWidth: 24 } }, score)
  );
}

function Modal({ open, onClose, children }) {
  if (!open) return null;
  return React.createElement('div', {
    onClick: onClose,
    style: { position: 'fixed', inset: 0, background: 'rgba(0,0,0,0.7)', zIndex: 100,
             display: 'flex', alignItems: 'center', justifyContent: 'center', padding: 16 }
  },
    React.createElement('div', {
      onClick: (e) => e.stopPropagation(),
      style: { background: '#0f172a', border: '1px solid #1e293b', borderRadius: 16, padding: 28,
               width: '100%', maxWidth: 480, maxHeight: '90vh', overflowY: 'auto' }
    }, children)
  );
}

// ─── MAIN APP ────────────────────────────────────────────────────────────
function StudyPlanner() {
  const defaultTasks = [
    { id: 1, name: "Calculus Problem Set", subject: "Math", type: "Assignment",
      dueDate: (() => { const d = new Date(); d.setDate(d.getDate()+3); return d.toISOString().split("T")[0]; })(),
      estimatedHours: 3, weight: 4, difficulty: 3 },
    { id: 2, name: "Midterm Exam Prep", subject: "History", type: "Test Prep",
      dueDate: (() => { const d = new Date(); d.setDate(d.getDate()+5); return d.toISOString().split("T")[0]; })(),
      estimatedHours: 6, weight: 5, difficulty: 4 },
    { id: 3, name: "Lab Report", subject: "Science", type: "Lab",
      dueDate: (() => { const d = new Date(); d.setDate(d.getDate()+2); return d.toISOString().split("T")[0]; })(),
      estimatedHours: 2, weight: 3, difficulty: 2 },
  ];

  const defaultSlots = [
    { id: 1, date: (() => { const d = new Date(); d.setDate(d.getDate()+0); return d.toISOString().split("T")[0]; })(), hours: 3 },
    { id: 2, date: (() => { const d = new Date(); d.setDate(d.getDate()+1); return d.toISOString().split("T")[0]; })(), hours: 2 },
    { id: 3, date: (() => { const d = new Date(); d.setDate(d.getDate()+2); return d.toISOString().split("T")[0]; })(), hours: 4 },
    { id: 4, date: (() => { const d = new Date(); d.setDate(d.getDate()+3); return d.toISOString().split("T")[0]; })(), hours: 2 },
  ];

  const [tasks, setTasks] = useState(() => loadFromStorage(STORAGE_KEY_TASKS, defaultTasks));
  const [slots, setSlots] = useState(() => loadFromStorage(STORAGE_KEY_SLOTS, defaultSlots));
  const [tab, setTab] = useState("tasks");
  const [taskModal, setTaskModal] = useState(false);
  const [slotModal, setSlotModal] = useState(false);
  const [newTask, setNewTask] = useState({ name: "", subject: "Math", type: "Assignment", dueDate: today(), estimatedHours: 2, weight: 3, difficulty: 2 });
  const [newSlot, setNewSlot] = useState({ date: today(), hours: 2 });

  // Save to localStorage on every change
  useEffect(() => { saveToStorage(STORAGE_KEY_TASKS, tasks); }, [tasks]);
  useEffect(() => { saveToStorage(STORAGE_KEY_SLOTS, slots); }, [slots]);

  const scoredTasks = useMemo(() =>
    tasks.map((t) => ({ ...t, priority: scorePriority({ ...t, daysUntilDue: daysFrom(t.dueDate) }) }))
      .sort((a, b) => b.priority - a.priority),
    [tasks]
  );

  const { schedule, infeasible } = useMemo(() => {
    const sortedSlots = [...slots].sort((a, b) => a.date.localeCompare(b.date));
    const enriched = tasks.map((t) => ({ ...t, daysUntilDue: daysFrom(t.dueDate) }));
    return generateSchedule(enriched, sortedSlots);
  }, [tasks, slots]);

  function addTask() {
    if (!newTask.name.trim()) return;
    setTasks([...tasks, { ...newTask, id: Date.now(), estimatedHours: +newTask.estimatedHours, weight: +newTask.weight, difficulty: +newTask.difficulty }]);
    setNewTask({ name: "", subject: "Math", type: "Assignment", dueDate: today(), estimatedHours: 2, weight: 3, difficulty: 2 });
    setTaskModal(false);
  }
  function addSlot() {
    setSlots([...slots, { ...newSlot, id: Date.now(), hours: +newSlot.hours }]);
    setNewSlot({ date: today(), hours: 2 });
    setSlotModal(false);
  }
  function removeTask(id) { setTasks(tasks.filter((t) => t.id !== id)); }
  function removeSlot(id) { setSlots(slots.filter((s) => s.id !== id)); }

  const inp = { background: "#1e293b", border: "1px solid #334155", borderRadius: 8, color: "#e2e8f0", padding: "8px 12px", width: "100%", fontSize: 13, outline: "none", boxSizing: "border-box" };
  const btn = (color = "#6366f1") => ({ background: color, border: "none", borderRadius: 8, color: "#fff", padding: "9px 18px", fontSize: 13, fontWeight: 700, cursor: "pointer", letterSpacing: 0.3 });

  return React.createElement('div', { style: { minHeight: "100vh", background: "#020817", color: "#e2e8f0", fontFamily: "'DM Mono', 'Courier New', monospace" } },
    // Header
    React.createElement('div', { style: { borderBottom: "1px solid #1e293b", padding: "20px 24px 0", background: "#0a0f1e" } },
      React.createElement('div', { style: { maxWidth: 900, margin: "0 auto" } },
        React.createElement('div', { style: { display: "flex", alignItems: "baseline", gap: 12, marginBottom: 4 } },
          React.createElement('h1', { style: { fontFamily: "Syne, sans-serif", fontSize: 26, fontWeight: 800, margin: 0, color: "#f8fafc", letterSpacing: -0.5 } }, "StudyOS"),
          React.createElement('span', { style: { fontSize: 11, color: "#6366f1", fontWeight: 500, letterSpacing: 2, textTransform: "uppercase" } }, "MCF Engine v1")
        ),
        React.createElement('p', { style: { margin: "0 0 16px", fontSize: 12, color: "#475569" } }, "Min‑cost flow scheduling — mathematical optimality, no AI needed"),
        React.createElement('div', { style: { display: "flex", gap: 0 } },
          ["tasks", "availability", "schedule"].map((t) =>
            React.createElement('button', {
              key: t,
              onClick: () => setTab(t),
              style: { background: "none", border: "none", borderBottom: tab === t ? "2px solid #6366f1" : "2px solid transparent", color: tab === t ? "#e2e8f0" : "#64748b", padding: "8px 20px", fontSize: 12, fontWeight: 600, cursor: "pointer", letterSpacing: 1, textTransform: "uppercase", transition: "all 0.15s" }
            }, t)
          )
        )
      )
    ),
    // Content
    React.createElement('div', { style: { maxWidth: 900, margin: "0 auto", padding: "24px 24px" } },
      tab === "tasks" && React.createElement(TasksTab, { scoredTasks, tasks, removeTask, setTaskModal, btn, inp }),
      tab === "availability" && React.createElement(AvailabilityTab, { slots, removeSlot, setSlotModal, btn, inp }),
      tab === "schedule" && React.createElement(ScheduleTab, { schedule, infeasible, btn })
    ),
    // Modals
    React.createElement(Modal, { open: taskModal, onClose: () => setTaskModal(false) },
      React.createElement('h3', { style: { margin: "0 0 20px", fontFamily: "Syne, sans-serif", fontSize: 18, color: "#f8fafc" } }, "Add Task"),
      React.createElement(TaskForm, { newTask, setNewTask, addTask, setTaskModal, inp, btn })
    ),
    React.createElement(Modal, { open: slotModal, onClose: () => setSlotModal(false) },
      React.createElement('h3', { style: { margin: "0 0 20px", fontFamily: "Syne, sans-serif", fontSize: 18, color: "#f8fafc" } }, "Add Study Slot"),
      React.createElement(SlotForm, { newSlot, setNewSlot, addSlot, setSlotModal, inp, btn })
    )
  );
}

// Sub-components for tabs (extracted for readability, all using React.createElement)
function TasksTab({ scoredTasks, tasks, removeTask, setTaskModal, btn, inp }) {
  return React.createElement('div', null,
    React.createElement('div', { style: { display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 20 } },
      React.createElement('div', null,
        React.createElement('div', { style: { fontSize: 14, fontWeight: 600, color: "#f8fafc" } }, "Your Tasks"),
        React.createElement('div', { style: { fontSize: 11, color: "#475569", marginTop: 2 } }, "Ranked by priority score algorithm")
      ),
      React.createElement('button', { onClick: () => setTaskModal(true), style: btn() }, "+ Add Task")
    ),
    React.createElement('div', { style: { background: "#0f172a", border: "1px solid #1e293b", borderRadius: 10, padding: "10px 16px", marginBottom: 16, fontSize: 11, color: "#64748b", display: "flex", gap: 20, flexWrap: "wrap" } },
      React.createElement('span', null, "Priority = ", React.createElement('span', { style: { color: "#f59e0b" } }, "urgency×3"), " + ", React.createElement('span', { style: { color: "#6366f1" } }, "weight×2"), " + ", React.createElement('span', { style: { color: "#10b981" } }, "difficulty×1.5"), " + time stress")
    ),
    React.createElement('div', { style: { display: "flex", flexDirection: "column", gap: 10 } },
      scoredTasks.length === 0 ? React.createElement('div', { style: { textAlign: "center", color: "#334155", padding: 40, fontSize: 13 } }, "No tasks yet. Add one to get started.") :
      scoredTasks.map((t, i) =>
        React.createElement('div', { key: t.id, style: { background: "#0f172a", border: "1px solid #1e293b", borderRadius: 12, padding: "14px 16px", display: "flex", gap: 14, alignItems: "flex-start" } },
          React.createElement('div', { style: { fontSize: 13, fontWeight: 800, color: "#334155", minWidth: 22, paddingTop: 2 } }, `#${i+1}`),
          React.createElement('div', { style: { flex: 1, minWidth: 0 } },
            React.createElement('div', { style: { display: "flex", alignItems: "center", gap: 8, flexWrap: "wrap", marginBottom: 6 } },
              React.createElement('span', { style: { fontSize: 13, fontWeight: 600, color: "#f8fafc" } }, t.name),
              React.createElement(Badge, { color: COLORS[t.subject] || "#64748b" }, t.subject),
              React.createElement(Badge, { color: "#334155" }, t.type)
            ),
            React.createElement(PriorityBar, { score: t.priority }),
            React.createElement('div', { style: { display: "flex", gap: 16, marginTop: 7, fontSize: 11, color: "#64748b", flexWrap: "wrap" } },
              React.createElement('span', null, "Due: ", React.createElement('span', { style: { color: daysFrom(t.dueDate) <= 2 ? "#ef4444" : "#94a3b8" } }, `${fmtDate(t.dueDate)} (${daysFrom(t.dueDate)}d)`)),
              React.createElement('span', null, `⏱ ${t.estimatedHours}h`),
              React.createElement('span', null, `Weight: ${t.weight}/5`),
              React.createElement('span', null, `Difficulty: ${DIFFICULTIES.find(d => d.v === t.difficulty)?.l}`)
            )
          ),
          React.createElement('button', { onClick: () => removeTask(t.id), style: { background: "none", border: "none", color: "#334155", cursor: "pointer", fontSize: 16, padding: 2, lineHeight: 1 } }, "✕")
        )
      )
    )
  );
}

function AvailabilityTab({ slots, removeSlot, setSlotModal, btn, inp }) {
  const sorted = [...slots].sort((a, b) => a.date.localeCompare(b.date));
  return React.createElement('div', null,
    React.createElement('div', { style: { display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 20 } },
      React.createElement('div', null,
        React.createElement('div', { style: { fontSize: 14, fontWeight: 600, color: "#f8fafc" } }, "Study Availability"),
        React.createElement('div', { style: { fontSize: 11, color: "#475569", marginTop: 2 } }, "Enter when and how long you can study")
      ),
      React.createElement('button', { onClick: () => setSlotModal(true), style: btn("#10b981") }, "+ Add Slot")
    ),
    React.createElement('div', { style: { display: "flex", flexDirection: "column", gap: 8 } },
      sorted.length === 0 ? React.createElement('div', { style: { textAlign: "center", color: "#334155", padding: 40, fontSize: 13 } }, "No slots yet. Add your available study times.") :
      sorted.map((s) =>
        React.createElement('div', { key: s.id, style: { background: "#0f172a", border: "1px solid #1e293b", borderRadius: 10, padding: "12px 16px", display: "flex", alignItems: "center", justifyContent: "space-between", gap: 12 } },
          React.createElement('div', { style: { display: "flex", gap: 12, alignItems: "center" } },
            React.createElement('div', { style: { width: 36, height: 36, background: "#1e293b", borderRadius: 8, display: "flex", alignItems: "center", justifyContent: "center", fontSize: 16 } }, "📅"),
            React.createElement('div', null,
              React.createElement('div', { style: { fontSize: 13, fontWeight: 600, color: "#f8fafc" } }, fmtDate(s.date)),
              React.createElement('div', { style: { fontSize: 11, color: "#64748b" } }, `${s.hours} hours available`)
            )
          ),
          React.createElement('div', { style: { display: "flex", alignItems: "center", gap: 10 } },
            React.createElement('div', { style: { display: "flex", gap: 2 } },
              Array.from({ length: Math.min(s.hours, 8) }).map((_, i) =>
                React.createElement('div', { key: i, style: { width: 8, height: 20, background: "#6366f1", borderRadius: 2, opacity: 0.6 + i * 0.05 } })
              )
            ),
            React.createElement('button', { onClick: () => removeSlot(s.id), style: { background: "none", border: "none", color: "#334155", cursor: "pointer", fontSize: 16, padding: 2 } }, "✕")
          )
        )
      )
    )
  );
}

function ScheduleTab({ schedule, infeasible, btn }) {
  return React.createElement('div', null,
    React.createElement('div', { style: { display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 20 } },
      React.createElement('div', null,
        React.createElement('div', { style: { fontSize: 14, fontWeight: 600, color: "#f8fafc" } }, "Generated Schedule"),
        React.createElement('div', { style: { fontSize: 11, color: "#475569", marginTop: 2 } }, "Optimal min‑cost flow assignment")
      )
    ),
    schedule.length === 0 ? React.createElement('div', { style: { textAlign: "center", color: "#334155", padding: 60, fontSize: 13 } }, "Add tasks and availability slots to generate your schedule.") :
    schedule.map((day, di) =>
      React.createElement('div', { key: di, style: { background: "#0f172a", border: "1px solid #1e293b", borderRadius: 14, overflow: "hidden", marginBottom: 16 } },
        React.createElement('div', { style: { background: "#1e293b", padding: "10px 18px", fontSize: 12, fontWeight: 700, color: "#94a3b8", letterSpacing: 1, textTransform: "uppercase", display: "flex", justifyContent: "space-between" } },
          React.createElement('span', null, fmtDate(day.date)),
          React.createElement('span', { style: { color: "#6366f1" } }, `${day.sessions.reduce((s, x) => s + x.hours, 0)}h planned`)
        ),
        React.createElement('div', { style: { padding: "12px 18px", display: "flex", flexDirection: "column", gap: 8 } },
          day.sessions.map((sess, si) =>
            React.createElement('div', { key: si, style: { display: "flex", alignItems: "center", gap: 12, padding: "10px 12px", background: "#0a0f1e", borderRadius: 9, borderLeft: `3px solid ${COLORS[sess.subject] || "#64748b"}` } },
              React.createElement('div', { style: { flex: 1 } },
                React.createElement('div', { style: { fontSize: 13, fontWeight: 600, color: "#f8fafc" } }, sess.taskName),
                React.createElement('div', { style: { fontSize: 11, color: "#64748b", marginTop: 2 } },
                  React.createElement(Badge, { color: COLORS[sess.subject] || "#64748b" }, sess.subject)
                )
              ),
              React.createElement('div', { style: { textAlign: "right" } },
                React.createElement('div', { style: { fontSize: 14, fontWeight: 700, color: "#e2e8f0" } }, `${sess.hours}h`),
                React.createElement('div', { style: { fontSize: 10, color: "#475569" } }, `priority ${sess.priority}`)
              )
            )
          )
        )
      )
    ),
    infeasible.length > 0 && React.createElement('div', { style: { marginTop: 20, background: "#1e0a0a", border: "1px solid #7f1d1d", borderRadius: 10, padding: 14 } },
      React.createElement('div', { style: { fontWeight: 700, color: "#fca5a5", marginBottom: 8, fontSize: 14 } }, "⚠️ Infeasible Tasks"),
      infeasible.map(item =>
        React.createElement('div', { key: item.id, style: { color: "#fecaca", fontSize: 12, marginBottom: 4 } },
          `${item.name}: requested ${item.requested}h, scheduled ${item.scheduled}h (shortfall ${item.shortfall}h) — ${item.reason}`
        )
      )
    )
  );
}

function TaskForm({ newTask, setNewTask, addTask, setTaskModal, inp, btn }) {
  return React.createElement('div', { style: { display: "flex", flexDirection: "column", gap: 12 } },
    React.createElement('div', null,
      React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "TASK NAME"),
      React.createElement('input', { style: inp, placeholder: "e.g. Chapter 5 Reading", value: newTask.name, onChange: (e) => setNewTask({ ...newTask, name: e.target.value }) })
    ),
    React.createElement('div', { style: { display: "grid", gridTemplateColumns: "1fr 1fr", gap: 10 } },
      React.createElement('div', null,
        React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "SUBJECT"),
        React.createElement('select', { style: inp, value: newTask.subject, onChange: (e) => setNewTask({ ...newTask, subject: e.target.value }) },
          SUBJECTS.map(s => React.createElement('option', { key: s }, s))
        )
      ),
      React.createElement('div', null,
        React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "TYPE"),
        React.createElement('select', { style: inp, value: newTask.type, onChange: (e) => setNewTask({ ...newTask, type: e.target.value }) },
          TASK_TYPES.map(t => React.createElement('option', { key: t }, t))
        )
      )
    ),
    React.createElement('div', null,
      React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "DUE DATE"),
      React.createElement('input', { type: "date", style: inp, value: newTask.dueDate, onChange: (e) => setNewTask({ ...newTask, dueDate: e.target.value }) })
    ),
    React.createElement('div', { style: { display: "grid", gridTemplateColumns: "1fr 1fr 1fr", gap: 10 } },
      React.createElement('div', null,
        React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "HOURS EST."),
        React.createElement('input', { type: "number", min: 0.5, max: 20, step: 0.5, style: inp, value: newTask.estimatedHours, onChange: (e) => setNewTask({ ...newTask, estimatedHours: e.target.value }) })
      ),
      React.createElement('div', null,
        React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "WEIGHT (1-5)"),
        React.createElement('input', { type: "number", min: 1, max: 5, style: inp, value: newTask.weight, onChange: (e) => setNewTask({ ...newTask, weight: e.target.value }) })
      ),
      React.createElement('div', null,
        React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "DIFFICULTY"),
        React.createElement('select', { style: inp, value: newTask.difficulty, onChange: (e) => setNewTask({ ...newTask, difficulty: +e.target.value }) },
          DIFFICULTIES.map(d => React.createElement('option', { key: d.v, value: d.v }, d.l))
        )
      )
    ),
    React.createElement('div', { style: { display: "flex", gap: 10, marginTop: 8 } },
      React.createElement('button', { onClick: () => setTaskModal(false), style: { ...btn("#334155"), flex: 1 } }, "Cancel"),
      React.createElement('button', { onClick: addTask, style: { ...btn(), flex: 1 } }, "Add Task")
    )
  );
}

function SlotForm({ newSlot, setNewSlot, addSlot, setSlotModal, inp, btn }) {
  return React.createElement('div', { style: { display: "flex", flexDirection: "column", gap: 12 } },
    React.createElement('div', null,
      React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "DATE"),
      React.createElement('input', { type: "date", style: inp, value: newSlot.date, onChange: (e) => setNewSlot({ ...newSlot, date: e.target.value }) })
    ),
    React.createElement('div', null,
      React.createElement('label', { style: { fontSize: 11, color: "#64748b", display: "block", marginBottom: 4 } }, "HOURS AVAILABLE"),
      React.createElement('input', { type: "number", min: 0.5, max: 12, step: 0.5, style: inp, value: newSlot.hours, onChange: (e) => setNewSlot({ ...newSlot, hours: e.target.value }) })
    ),
    React.createElement('div', { style: { display: "flex", gap: 10, marginTop: 8 } },
      React.createElement('button', { onClick: () => setSlotModal(false), style: { ...btn("#334155"), flex: 1 } }, "Cancel"),
      React.createElement('button', { onClick: addSlot, style: { ...btn("#10b981"), flex: 1 } }, "Add Slot")
    )
  );
}

// ─── Render ──────────────────────────────────────────────────────────────
ReactDOM.createRoot(document.getElementById('root')).render(React.createElement(StudyPlanner));
