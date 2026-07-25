// ═══════════════════════════════════════════════════════════════
// MentalMap — Neural Note-Taking Application
// Force-directed brain graph with Obsidian-style UI
// Integrated with Firebase Realtime Database
// ═══════════════════════════════════════════════════════════════

import { initializeApp } from "https://www.gstatic.com/firebasejs/10.8.1/firebase-app.js";
import { getDatabase, ref, set, onValue, off } from "https://www.gstatic.com/firebasejs/10.8.1/firebase-database.js";
import { getAuth, signInWithEmailAndPassword, createUserWithEmailAndPassword, signOut, onAuthStateChanged } from "https://www.gstatic.com/firebasejs/10.8.1/firebase-auth.js";

// Your web app's Firebase configuration
const firebaseConfig = {
  apiKey: "AIzaSyCMZ6gCI6bDOKLscw3BzuC7B-VAZ3rOyBA",
  authDomain: "antigravity-opus-3541a.firebaseapp.com",
  projectId: "antigravity-opus-3541a",
  storageBucket: "antigravity-opus-3541a.firebasestorage.app",
  messagingSenderId: "464729577487",
  appId: "1:464729577487:web:aed5717f779d2314572b7a",
  measurementId: "G-9GX4749JGG"
};

// Initialize Firebase
const app = initializeApp(firebaseConfig);
const db = getDatabase(app);
const auth = getAuth(app);

// ─── Constants ───────────────────────────────────────────────
const NODE_COLORS = [
    '#7aa2f7', '#bb9af7', '#7dcfff', '#9ece6a',
    '#ff9e64', '#f7768e', '#e0af68', '#73daca',
];

const PHYSICS = {
    REPULSION:    6000,
    ATTRACTION:   0.008,
    GRAVITY:      0.015,
    DAMPING:      0.88,
    MIN_DIST:     100,
    MAX_SPEED:    6,
    SETTLE_THRESHOLD: 0.05,
};

const RENDER = {
    NODE_RADIUS_MIN:  20,
    NODE_RADIUS_MAX:  40,
    CONN_WIDTH:       1.8,
    GLOW_BLUR:        18,
    PARTICLE_COUNT:   2,
    PARTICLE_SPEED:   0.002,
    GRID_SIZE:        50,
    GRID_DOT_SIZE:    1,
    GRID_OPACITY:     0.08,
    LABEL_FONT:       '11px Inter, sans-serif',
    BG_COLOR:         '#0d1017',
};

let DB_KEY = null; // Will be set upon login
const AUTOSAVE_INTERVAL = 800;  // ms debounce

// ─── Utility ─────────────────────────────────────────────────
const $ = (sel) => document.querySelector(sel);
const $$ = (sel) => document.querySelectorAll(sel);
const clamp = (v, min, max) => Math.max(min, Math.min(max, v));
const lerp = (a, b, t) => a + (b - a) * t;
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 8);

function formatDate(iso) {
    if (!iso) return "—";
    const d = new Date(iso);
    const pad = (n) => String(n).padStart(2, '0');
    return `${pad(d.getDate())}/${pad(d.getMonth() + 1)}/${d.getFullYear()} ${pad(d.getHours())}:${pad(d.getMinutes())}`;
}

function sanitizeFilename(name) {
    return name.replace(/[<>:"/\\|?*\x00-\x1f]/g, '_').trim() || 'nota';
}


// ═══════════════════════════════════════════════════════════════
// Vector2D
// ═══════════════════════════════════════════════════════════════
class Vec2 {
    constructor(x = 0, y = 0) { this.x = x; this.y = y; }
    add(v)  { return new Vec2(this.x + v.x, this.y + v.y); }
    sub(v)  { return new Vec2(this.x - v.x, this.y - v.y); }
    mul(s)  { return new Vec2(this.x * s, this.y * s); }
    div(s)  { return s ? new Vec2(this.x / s, this.y / s) : new Vec2(); }
    mag()   { return Math.sqrt(this.x * this.x + this.y * this.y); }
    magSq() { return this.x * this.x + this.y * this.y; }
    norm()  { const m = this.mag(); return m > 0 ? this.div(m) : new Vec2(); }
    dist(v) { return this.sub(v).mag(); }
    copy()  { return new Vec2(this.x, this.y); }
    limit(max) {
        if (this.magSq() > max * max) return this.norm().mul(max);
        return this.copy();
    }
    static random(range = 1) {
        const a = Math.random() * Math.PI * 2;
        const r = Math.random() * range;
        return new Vec2(Math.cos(a) * r, Math.sin(a) * r);
    }
}


// ═══════════════════════════════════════════════════════════════
// Particle (flows along edges)
// ═══════════════════════════════════════════════════════════════
class Particle {
    constructor() {
        this.t = Math.random();
        this.speed = RENDER.PARTICLE_SPEED * (0.6 + Math.random() * 0.8);
        this.size = 1.2 + Math.random() * 1.5;
        this.opacity = 0.3 + Math.random() * 0.5;
    }
    update() {
        this.t += this.speed;
        if (this.t > 1) this.t -= 1;
    }
}


// ═══════════════════════════════════════════════════════════════
// BrainGraph — Force-directed graph + Canvas renderer
// ═══════════════════════════════════════════════════════════════
class BrainGraph {
    constructor(canvas) {
        this.canvas  = canvas;
        this.ctx     = canvas.getContext('2d');
        this.nodes   = new Map();   // id -> { id, pos, vel, radius, color, label, pinned }
        this.edges   = [];          // [{ from, to, particles }]
        this.camera  = { x: 0, y: 0, zoom: 1 };
        this.targetCamera = { x: 0, y: 0, zoom: 1 };

        // Interaction state
        this.dragging     = null;   // node id being dragged
        this.panning      = false;
        this.panStart     = null;
        this.panCameraStart = null;
        this.hoveredNode  = null;
        this.selectedNode = null;
        this.mouseWorld   = new Vec2();
        this.mouseScreen  = new Vec2();

        // Animation
        this.time = 0;
        this.running = true;

        this._resize();
        this._bindEvents();
        this._loop();
    }

    // ── Coordinate transforms ──
    screenToWorld(sx, sy) {
        return new Vec2(
            (sx - this.w / 2) / this.camera.zoom + this.camera.x,
            (sy - this.h / 2) / this.camera.zoom + this.camera.y
        );
    }
    worldToScreen(wx, wy) {
        return new Vec2(
            (wx - this.camera.x) * this.camera.zoom + this.w / 2,
            (wy - this.camera.y) * this.camera.zoom + this.h / 2
        );
    }

    // ── Node Management ──
    addNode(id, label, color, x, y, radius) {
        this.nodes.set(id, {
            id, label, color, radius,
            pos: new Vec2(x ?? (Math.random() - 0.5) * 300, y ?? (Math.random() - 0.5) * 300),
            vel: new Vec2(),
            pinned: false,
        });
    }

    removeNode(id) {
        this.nodes.delete(id);
        this.edges = this.edges.filter(e => e.from !== id && e.to !== id);
        if (this.selectedNode === id) this.selectedNode = null;
        if (this.hoveredNode === id) this.hoveredNode = null;
        if (this.dragging === id) this.dragging = null;
    }

    updateNode(id, props) {
        const n = this.nodes.get(id);
        if (!n) return;
        if (props.label !== undefined)  n.label  = props.label;
        if (props.color !== undefined)  n.color  = props.color;
        if (props.radius !== undefined) n.radius = props.radius;
    }

    addEdge(fromId, toId) {
        if (fromId === toId) return;
        const exists = this.edges.some(e =>
            (e.from === fromId && e.to === toId) ||
            (e.from === toId && e.to === fromId)
        );
        if (exists) return;
        const particles = [];
        for (let i = 0; i < RENDER.PARTICLE_COUNT; i++) {
            particles.push(new Particle());
        }
        this.edges.push({ from: fromId, to: toId, particles });
    }

    removeEdge(fromId, toId) {
        this.edges = this.edges.filter(e =>
            !((e.from === fromId && e.to === toId) ||
              (e.from === toId && e.to === fromId))
        );
    }

    hasEdge(fromId, toId) {
        return this.edges.some(e =>
            (e.from === fromId && e.to === toId) ||
            (e.from === toId && e.to === fromId)
        );
    }

    // ── Physics Simulation ──
    simulate() {
        const nodes = [...this.nodes.values()];
        const n = nodes.length;
        if (n === 0) return;

        // Repulsion (Coulomb)
        for (let i = 0; i < n; i++) {
            for (let j = i + 1; j < n; j++) {
                const a = nodes[i], b = nodes[j];
                const diff = a.pos.sub(b.pos);
                let dist = diff.mag();
                if (dist < 1) dist = 1;
                const minD = (a.radius + b.radius) * 1.5 + PHYSICS.MIN_DIST;
                if (dist < minD * 3) {
                    const force = diff.norm().mul(PHYSICS.REPULSION / (dist * dist));
                    if (!a.pinned) a.vel = a.vel.add(force);
                    if (!b.pinned) b.vel = b.vel.sub(force);
                }
            }
        }

        // Attraction (Hooke along edges)
        for (const edge of this.edges) {
            const a = this.nodes.get(edge.from);
            const b = this.nodes.get(edge.to);
            if (!a || !b) continue;
            const diff = b.pos.sub(a.pos);
            const dist = diff.mag();
            const ideal = (a.radius + b.radius) * 2 + 80;
            const displacement = dist - ideal;
            const force = diff.norm().mul(displacement * PHYSICS.ATTRACTION);
            if (!a.pinned) a.vel = a.vel.add(force);
            if (!b.pinned) b.vel = b.vel.sub(force);
        }

        // Gravity toward center
        for (const node of nodes) {
            if (node.pinned) continue;
            const toCenter = node.pos.mul(-1);
            node.vel = node.vel.add(toCenter.mul(PHYSICS.GRAVITY));
        }

        // Integrate
        for (const node of nodes) {
            if (node.pinned) continue;
            node.vel = node.vel.mul(PHYSICS.DAMPING).limit(PHYSICS.MAX_SPEED);
            node.pos = node.pos.add(node.vel);
        }

        // Update particles
        for (const edge of this.edges) {
            for (const p of edge.particles) p.update();
        }
    }

    // ── Rendering ──
    render() {
        const { ctx, w, h } = this;
        const dpr = window.devicePixelRatio || 1;

        // Smooth camera
        this.camera.x    = lerp(this.camera.x,    this.targetCamera.x,    0.08);
        this.camera.y    = lerp(this.camera.y,    this.targetCamera.y,    0.08);
        this.camera.zoom = lerp(this.camera.zoom, this.targetCamera.zoom, 0.08);

        ctx.save();
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

        // Background
        ctx.fillStyle = RENDER.BG_COLOR;
        ctx.fillRect(0, 0, w, h);

        // Grid dots
        this._drawGrid();

        // Transform to world
        ctx.save();
        ctx.translate(w / 2, h / 2);
        ctx.scale(this.camera.zoom, this.camera.zoom);
        ctx.translate(-this.camera.x, -this.camera.y);

        // Draw edges
        this._drawEdges();

        // Draw nodes
        this._drawNodes();

        ctx.restore();
        ctx.restore();
    }

    _drawGrid() {
        const { ctx, w, h, camera } = this;
        const gs = RENDER.GRID_SIZE * camera.zoom;
        if (gs < 8) return;  // Don't draw when zoomed out too far

        const offsetX = (w / 2 - camera.x * camera.zoom) % gs;
        const offsetY = (h / 2 - camera.y * camera.zoom) % gs;

        ctx.fillStyle = `rgba(122, 162, 247, ${RENDER.GRID_OPACITY * Math.min(1, camera.zoom)})`;

        for (let x = offsetX; x < w; x += gs) {
            for (let y = offsetY; y < h; y += gs) {
                ctx.beginPath();
                ctx.arc(x, y, RENDER.GRID_DOT_SIZE, 0, Math.PI * 2);
                ctx.fill();
            }
        }
    }

    _drawEdges() {
        const { ctx } = this;
        const time = this.time;

        for (const edge of this.edges) {
            const a = this.nodes.get(edge.from);
            const b = this.nodes.get(edge.to);
            if (!a || !b) continue;

            const ax = a.pos.x, ay = a.pos.y;
            const bx = b.pos.x, by = b.pos.y;

            // Curved bezier
            const mx = (ax + bx) / 2;
            const my = (ay + by) / 2;
            const dx = bx - ax, dy = by - ay;
            const dist = Math.sqrt(dx * dx + dy * dy);
            const curveStrength = Math.min(dist * 0.15, 40);
            const nx = -dy / (dist || 1) * curveStrength;
            const ny =  dx / (dist || 1) * curveStrength;
            const cpx = mx + nx, cpy = my + ny;

            // Glow
            ctx.save();
            ctx.strokeStyle = a.color;
            ctx.globalAlpha = 0.08;
            ctx.lineWidth = 8;
            ctx.shadowColor = a.color;
            ctx.shadowBlur = 15;
            ctx.beginPath();
            ctx.moveTo(ax, ay);
            ctx.quadraticCurveTo(cpx, cpy, bx, by);
            ctx.stroke();
            ctx.restore();

            // Main line
            const grad = ctx.createLinearGradient(ax, ay, bx, by);
            grad.addColorStop(0, a.color + '80');
            grad.addColorStop(1, b.color + '80');

            ctx.strokeStyle = grad;
            ctx.lineWidth = RENDER.CONN_WIDTH;
            ctx.globalAlpha = 0.6;
            ctx.beginPath();
            ctx.moveTo(ax, ay);
            ctx.quadraticCurveTo(cpx, cpy, bx, by);
            ctx.stroke();
            ctx.globalAlpha = 1;

            // Particles
            for (const p of edge.particles) {
                const t = p.t;
                const tt = 1 - t;
                const px = tt * tt * ax + 2 * tt * t * cpx + t * t * bx;
                const py = tt * tt * ay + 2 * tt * t * cpy + t * t * by;

                ctx.fillStyle = a.color;
                ctx.globalAlpha = p.opacity * (0.6 + 0.4 * Math.sin(time * 3 + p.t * 10));
                ctx.beginPath();
                ctx.arc(px, py, p.size * this.camera.zoom, 0, Math.PI * 2);
                ctx.fill();
                ctx.globalAlpha = 1;
            }
        }
    }

    _drawNodes() {
        const { ctx } = this;
        const time = this.time;
        const nodes = [...this.nodes.values()];

        for (const node of nodes) {
            const { pos, radius, color, label, id } = node;
            const x = pos.x, y = pos.y;
            const isHovered  = this.hoveredNode === id;
            const isSelected = this.selectedNode === id;
            const effectiveR = radius * (isHovered ? 1.12 : 1);

            // Outer glow ring
            if (isSelected || isHovered) {
                const pulseR = effectiveR + 8 + Math.sin(time * 3) * 3;
                ctx.beginPath();
                ctx.arc(x, y, pulseR, 0, Math.PI * 2);
                ctx.strokeStyle = color;
                ctx.lineWidth = 2;
                ctx.globalAlpha = isSelected ? 0.5 : 0.3;
                ctx.stroke();
                ctx.globalAlpha = 1;
            }

            // Ambient glow
            const glowGrad = ctx.createRadialGradient(x, y, effectiveR * 0.5, x, y, effectiveR * 2.5);
            glowGrad.addColorStop(0, color + '25');
            glowGrad.addColorStop(1, color + '00');
            ctx.fillStyle = glowGrad;
            ctx.beginPath();
            ctx.arc(x, y, effectiveR * 2.5, 0, Math.PI * 2);
            ctx.fill();

            // Node body
            const bodyGrad = ctx.createRadialGradient(
                x - effectiveR * 0.3, y - effectiveR * 0.3, 0,
                x, y, effectiveR
            );
            bodyGrad.addColorStop(0, color + 'dd');
            bodyGrad.addColorStop(0.7, color + '99');
            bodyGrad.addColorStop(1, color + '55');
            ctx.fillStyle = bodyGrad;
            ctx.beginPath();
            ctx.arc(x, y, effectiveR, 0, Math.PI * 2);
            ctx.fill();

            // Inner highlight
            ctx.beginPath();
            ctx.arc(x - effectiveR * 0.25, y - effectiveR * 0.25, effectiveR * 0.35, 0, Math.PI * 2);
            ctx.fillStyle = 'rgba(255,255,255,0.12)';
            ctx.fill();

            // Border
            ctx.beginPath();
            ctx.arc(x, y, effectiveR, 0, Math.PI * 2);
            ctx.strokeStyle = isSelected ? '#ffffff55' : color + '40';
            ctx.lineWidth = isSelected ? 2 : 1;
            ctx.stroke();

            // Label
            ctx.font = RENDER.LABEL_FONT;
            ctx.textAlign = 'center';
            ctx.textBaseline = 'top';
            const labelY = y + effectiveR + 8;
            const text = label.length > 18 ? label.slice(0, 16) + '…' : label;

            // Label shadow
            ctx.fillStyle = RENDER.BG_COLOR;
            ctx.globalAlpha = 0.7;
            const metrics = ctx.measureText(text);
            ctx.fillRect(
                x - metrics.width / 2 - 4,
                labelY - 2,
                metrics.width + 8,
                16
            );
            ctx.globalAlpha = 1;

            // Label text
            ctx.fillStyle = isSelected || isHovered ? '#e0e5f5' : '#9aa5ce';
            ctx.fillText(text, x, labelY);
        }
    }

    // ── Hit Testing ──
    _nodeAt(worldPos) {
        const nodes = [...this.nodes.values()].reverse();
        for (const node of nodes) {
            const dist = node.pos.dist(worldPos);
            if (dist <= node.radius + 5) return node;
        }
        return null;
    }

    // ── Camera ──
    zoomTo(level) {
        this.targetCamera.zoom = clamp(level, 0.15, 4);
    }

    zoomBy(delta) {
        this.zoomTo(this.targetCamera.zoom * (1 + delta));
    }

    panTo(x, y) {
        this.targetCamera.x = x;
        this.targetCamera.y = y;
    }

    fitAll(padding = 80) {
        const nodes = [...this.nodes.values()];
        if (nodes.length === 0) {
            this.panTo(0, 0);
            this.zoomTo(1);
            return;
        }
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
        for (const n of nodes) {
            minX = Math.min(minX, n.pos.x - n.radius);
            minY = Math.min(minY, n.pos.y - n.radius);
            maxX = Math.max(maxX, n.pos.x + n.radius);
            maxY = Math.max(maxY, n.pos.y + n.radius);
        }
        const cx = (minX + maxX) / 2;
        const cy = (minY + maxY) / 2;
        const graphW = maxX - minX + padding * 2;
        const graphH = maxY - minY + padding * 2;
        const zoom = Math.min(this.w / graphW, this.h / graphH, 2);

        this.panTo(cx, cy);
        this.zoomTo(clamp(zoom, 0.2, 2));
    }

    focusNode(id) {
        const node = this.nodes.get(id);
        if (!node) return;
        this.panTo(node.pos.x, node.pos.y);
        this.zoomTo(clamp(this.camera.zoom, 0.8, 1.5));
    }

    // ── Event Binding ──
    _bindEvents() {
        const canvas = this.canvas;

        // Resize
        this._resizeHandler = () => this._resize();
        window.addEventListener('resize', this._resizeHandler);

        // Mouse
        canvas.addEventListener('mousedown',  (e) => this._onMouseDown(e));
        canvas.addEventListener('mousemove',  (e) => this._onMouseMove(e));
        canvas.addEventListener('mouseup',    (e) => this._onMouseUp(e));
        canvas.addEventListener('mouseleave', ()  => this._onMouseLeave());
        canvas.addEventListener('wheel',      (e) => this._onWheel(e), { passive: false });
        canvas.addEventListener('dblclick',   (e) => this._onDblClick(e));

        // Touch
        canvas.addEventListener('touchstart',  (e) => this._onTouchStart(e), { passive: false });
        canvas.addEventListener('touchmove',   (e) => this._onTouchMove(e), { passive: false });
        canvas.addEventListener('touchend',    (e) => this._onTouchEnd(e));
    }

    _getCanvasPos(e) {
        const rect = this.canvas.getBoundingClientRect();
        return { x: e.clientX - rect.left, y: e.clientY - rect.top };
    }

    _onMouseDown(e) {
        const { x, y } = this._getCanvasPos(e);
        const world = this.screenToWorld(x, y);
        const node = this._nodeAt(world);

        if (node) {
            this.dragging = node.id;
            node.pinned = true;
            this.canvas.className = 'cursor-grabbing';
        } else {
            this.panning = true;
            this.panStart = { x: e.clientX, y: e.clientY };
            this.panCameraStart = { x: this.targetCamera.x, y: this.targetCamera.y };
            this.canvas.className = 'cursor-grabbing';
        }
    }

    _onMouseMove(e) {
        const { x, y } = this._getCanvasPos(e);
        this.mouseScreen = new Vec2(x, y);
        this.mouseWorld = this.screenToWorld(x, y);

        if (this.dragging) {
            const node = this.nodes.get(this.dragging);
            if (node) {
                node.pos = this.mouseWorld.copy();
                node.vel = new Vec2();
            }
        } else if (this.panning) {
            const dx = (e.clientX - this.panStart.x) / this.camera.zoom;
            const dy = (e.clientY - this.panStart.y) / this.camera.zoom;
            this.targetCamera.x = this.panCameraStart.x - dx;
            this.targetCamera.y = this.panCameraStart.y - dy;
        } else {
            // Hover detection
            const node = this._nodeAt(this.mouseWorld);
            const newHovered = node ? node.id : null;
            if (newHovered !== this.hoveredNode) {
                this.hoveredNode = newHovered;
                this.canvas.className = newHovered ? 'cursor-pointer' : 'cursor-grab';

                // Update tooltip
                if (this.onHover) this.onHover(newHovered, x, y);
            }
        }
    }

    _onMouseUp(e) {
        if (this.dragging) {
            const node = this.nodes.get(this.dragging);
            if (node) {
                node.pinned = false;
                // If barely moved, treat as click
                if (this.onClick) this.onClick(this.dragging);
            }
            this.dragging = null;
            
            // Notify position update on drag end
            if (window.app) window.app._scheduleSave();
        }
        if (this.panning) {
            this.panning = false;
        }
        this.canvas.className = this.hoveredNode ? 'cursor-pointer' : 'cursor-grab';
    }

    _onMouseLeave() {
        this.hoveredNode = null;
        this.panning = false;
        if (this.dragging) {
            const node = this.nodes.get(this.dragging);
            if (node) node.pinned = false;
            this.dragging = null;
            if (window.app) window.app._scheduleSave();
        }
        if (this.onHover) this.onHover(null, 0, 0);
        this.canvas.className = 'cursor-grab';
    }

    _onWheel(e) {
        e.preventDefault();
        const delta = -e.deltaY * 0.001;
        const { x, y } = this._getCanvasPos(e);
        const worldBefore = this.screenToWorld(x, y);

        this.zoomBy(delta);

        // Zoom toward mouse
        const worldAfter = this.screenToWorld(x, y);
        const diff = worldBefore.sub(worldAfter);
        this.targetCamera.x += diff.x;
        this.targetCamera.y += diff.y;
    }

    _onDblClick(e) {
        const { x, y } = this._getCanvasPos(e);
        const world = this.screenToWorld(x, y);
        const node = this._nodeAt(world);
        if (!node && this.onDoubleClick) {
            this.onDoubleClick(world.x, world.y);
        }
    }

    // Touch handling
    _lastTouchDist = 0;
    _onTouchStart(e) {
        e.preventDefault();
        if (e.touches.length === 1) {
            const t = e.touches[0];
            const rect = this.canvas.getBoundingClientRect();
            const x = t.clientX - rect.left, y = t.clientY - rect.top;
            const world = this.screenToWorld(x, y);
            const node = this._nodeAt(world);
            if (node) {
                this.dragging = node.id;
                node.pinned = true;
            } else {
                this.panning = true;
                this.panStart = { x: t.clientX, y: t.clientY };
                this.panCameraStart = { x: this.targetCamera.x, y: this.targetCamera.y };
            }
        } else if (e.touches.length === 2) {
            const dx = e.touches[0].clientX - e.touches[1].clientX;
            const dy = e.touches[0].clientY - e.touches[1].clientY;
            this._lastTouchDist = Math.sqrt(dx * dx + dy * dy);
        }
    }

    _onTouchMove(e) {
        e.preventDefault();
        if (e.touches.length === 1) {
            const t = e.touches[0];
            const rect = this.canvas.getBoundingClientRect();
            const x = t.clientX - rect.left, y = t.clientY - rect.top;
            if (this.dragging) {
                const world = this.screenToWorld(x, y);
                const node = this.nodes.get(this.dragging);
                if (node) { node.pos = world.copy(); node.vel = new Vec2(); }
            } else if (this.panning) {
                const dx = (t.clientX - this.panStart.x) / this.camera.zoom;
                const dy = (t.clientY - this.panStart.y) / this.camera.zoom;
                this.targetCamera.x = this.panCameraStart.x - dx;
                this.targetCamera.y = this.panCameraStart.y - dy;
            }
        } else if (e.touches.length === 2) {
            const dx = e.touches[0].clientX - e.touches[1].clientX;
            const dy = e.touches[0].clientY - e.touches[1].clientY;
            const dist = Math.sqrt(dx * dx + dy * dy);
            if (this._lastTouchDist > 0) {
                const scale = dist / this._lastTouchDist;
                this.zoomTo(this.targetCamera.zoom * scale);
            }
            this._lastTouchDist = dist;
        }
    }

    _onTouchEnd(e) {
        if (this.dragging) {
            const node = this.nodes.get(this.dragging);
            if (node) {
                node.pinned = false;
                if (this.onClick) this.onClick(this.dragging);
            }
            this.dragging = null;
            if (window.app) window.app._scheduleSave();
        }
        this.panning = false;
        this._lastTouchDist = 0;
    }

    // ── Resize ──
    _resize() {
        const dpr = window.devicePixelRatio || 1;
        const rect = this.canvas.parentElement.getBoundingClientRect();
        this.w = rect.width;
        this.h = rect.height;
        this.canvas.width  = this.w * dpr;
        this.canvas.height = this.h * dpr;
        this.canvas.style.width  = this.w + 'px';
        this.canvas.style.height = this.h + 'px';
    }

    // ── Main Loop ──
    _loop() {
        if (!this.running) return;
        this.time = performance.now() / 1000;
        this.simulate();
        this.render();
        requestAnimationFrame(() => this._loop());
    }

    destroy() {
        this.running = false;
        window.removeEventListener('resize', this._resizeHandler);
    }
}


// ═══════════════════════════════════════════════════════════════
// Toast System
// ═══════════════════════════════════════════════════════════════
class Toast {
    static container = null;

    static init() {
        this.container = $('#toastContainer');
    }

    static show(message, type = 'info', duration = 3000) {
        if (!this.container) this.init();

        const colors = {
            info:    { bg: 'rgba(122,162,247,0.12)', border: 'rgba(122,162,247,0.3)', text: '#7aa2f7', icon: 'ℹ' },
            success: { bg: 'rgba(158,206,106,0.12)', border: 'rgba(158,206,106,0.3)', text: '#9ece6a', icon: '✓' },
            error:   { bg: 'rgba(247,118,142,0.12)', border: 'rgba(247,118,142,0.3)', text: '#f7768e', icon: '✕' },
            warning: { bg: 'rgba(224,175,104,0.12)', border: 'rgba(224,175,104,0.3)', text: '#e0af68', icon: '⚠' },
        };
        const c = colors[type] || colors.info;

        const el = document.createElement('div');
        el.className = 'toast pointer-events-auto';
        el.style.cssText = `
            background: ${c.bg};
            backdrop-filter: blur(16px);
            border: 1px solid ${c.border};
            border-radius: 12px;
            padding: 10px 16px;
            font-size: 13px;
            color: ${c.text};
            display: flex;
            align-items: center;
            gap: 8px;
            box-shadow: 0 8px 32px rgba(0,0,0,0.3);
            max-width: 360px;
            font-family: 'Inter', sans-serif;
        `;
        el.innerHTML = `
            <span style="font-size: 16px; font-weight: 700;">${c.icon}</span>
            <span style="flex: 1;">${message}</span>
        `;

        this.container.appendChild(el);

        setTimeout(() => {
            el.classList.add('removing');
            el.addEventListener('animationend', () => el.remove());
        }, duration);
    }
}


// ═══════════════════════════════════════════════════════════════
// Modal Helper
// ═══════════════════════════════════════════════════════════════
class Modal {
    static open(modalEl) {
        modalEl.classList.remove('hidden');
        modalEl.classList.add('flex');
        // Trigger animation
        requestAnimationFrame(() => {
            const backdrop = modalEl.querySelector('.modal-backdrop');
            const card = modalEl.querySelector('.modal-card');
            if (backdrop) backdrop.classList.add('active');
            if (card) card.classList.add('active');
        });
        // Focus first input
        const input = modalEl.querySelector('input');
        if (input) setTimeout(() => input.focus(), 100);
    }

    static close(modalEl) {
        const backdrop = modalEl.querySelector('.modal-backdrop');
        const card = modalEl.querySelector('.modal-card');
        if (backdrop) backdrop.classList.remove('active');
        if (card) card.classList.remove('active');
        setTimeout(() => {
            modalEl.classList.add('hidden');
            modalEl.classList.remove('flex');
        }, 200);
    }
}


// ═══════════════════════════════════════════════════════════════
// MentalMap App
// ═══════════════════════════════════════════════════════════════
class MentalMapApp {
    constructor() {
        this.notes = new Map();   // id -> { id, title, content, color, connections[], createdAt, updatedAt, x, y }
        this.selectedNoteId = null;
        this.colorIndex = 0;
        this._saveTimer = null;
        this._isInitialLoad = true;
        this.currentUser = null;

        // Init components
        Toast.init();
        this.graph = new BrainGraph($('#brainCanvas'));

        // Graph callbacks
        this.graph.onClick  = (id) => this.selectNote(id);
        this.graph.onHover  = (id, sx, sy) => this._updateTooltip(id, sx, sy);
        this.graph.onDoubleClick = (wx, wy) => this.openNewNoteModal(wx, wy);

        // Bind Auth and wait for state
        this._bindAuth();

        // Bind UI
        this._bindUI();
    }

    // ── Auth ──
    _bindAuth() {
        const authOverlay = $('#authOverlay');
        const authForm = $('#authForm');
        const emailInput = $('#authEmail');
        const passInput = $('#authPassword');
        const btnLogin = $('#btnLogin');
        const btnRegister = $('#btnRegister');
        const btnLogout = $('#btnLogout');

        onAuthStateChanged(auth, (user) => {
            if (user) {
                // Logged in
                this.currentUser = user;
                authOverlay.classList.add('hidden');
                btnLogout.classList.remove('hidden');
                
                // Initialize database
                DB_KEY = `users/${user.uid}/data`;
                this._listenFirebase();
            } else {
                // Logged out
                this.currentUser = null;
                authOverlay.classList.remove('hidden');
                btnLogout.classList.add('hidden');
                
                // Disconnect DB
                if (DB_KEY) {
                    off(ref(db, DB_KEY));
                }
                
                // Clear UI
                this.notes.clear();
                this.graph.nodes.clear();
                this.graph.edges = [];
                this._renderSidebar();
                this._updateEmptyState();
                this._closeEditor();
            }
        });

        authForm.addEventListener('submit', async (e) => {
            e.preventDefault();
            const email = emailInput.value.trim();
            const pass = passInput.value;
            try {
                btnLogin.disabled = true;
                btnLogin.textContent = 'Carregando...';
                await signInWithEmailAndPassword(auth, email, pass);
                Toast.show('Bem-vindo de volta!', 'success');
                emailInput.value = '';
                passInput.value = '';
            } catch (error) {
                console.error(error);
                Toast.show('Erro ao entrar: ' + error.message, 'error');
            } finally {
                btnLogin.disabled = false;
                btnLogin.textContent = 'Entrar';
            }
        });

        btnRegister.addEventListener('click', async () => {
            const email = emailInput.value.trim();
            const pass = passInput.value;
            if (!email || pass.length < 6) {
                Toast.show('Insira um e-mail válido e uma senha com 6+ caracteres.', 'warning');
                return;
            }
            try {
                btnRegister.disabled = true;
                btnRegister.textContent = 'Criando...';
                await createUserWithEmailAndPassword(auth, email, pass);
                Toast.show('Conta criada com sucesso!', 'success');
                emailInput.value = '';
                passInput.value = '';
            } catch (error) {
                console.error(error);
                Toast.show('Erro ao registrar: ' + error.message, 'error');
            } finally {
                btnRegister.disabled = false;
                btnRegister.textContent = 'Criar Nova Conta';
            }
        });

        btnLogout.addEventListener('click', async () => {
            try {
                await signOut(auth);
                Toast.show('Você saiu da conta.', 'info');
            } catch (error) {
                console.error(error);
                Toast.show('Erro ao sair.', 'error');
            }
        });
    }

    // ── Note CRUD ──
    createNote(title, wx, wy) {
        const id = uid();
        const now = new Date().toISOString();
        const color = NODE_COLORS[this.colorIndex % NODE_COLORS.length];
        this.colorIndex++;

        const note = {
            id,
            title: title || 'Nova Nota',
            content: '',
            color,
            connections: [],
            createdAt: now,
            updatedAt: now,
            x: wx ?? (Math.random() - 0.5) * 400,
            y: wy ?? (Math.random() - 0.5) * 400,
        };

        this.notes.set(id, note);

        // Determine radius
        const radius = this._noteRadius(note);

        // Add to graph
        this.graph.addNode(id, note.title, note.color, note.x, note.y, radius);

        // Auto-connect to last note
        const allNotes = [...this.notes.values()];
        if (allNotes.length > 1) {
            // Find nearest note for connection
            let nearest = null;
            let nearestDist = Infinity;
            for (const other of allNotes) {
                if (other.id === id) continue;
                const dx = other.x - note.x;
                const dy = other.y - note.y;
                const dist = Math.sqrt(dx * dx + dy * dy);
                if (dist < nearestDist) {
                    nearestDist = dist;
                    nearest = other;
                }
            }
            if (nearest) {
                this._connect(id, nearest.id);
            }
        }

        this._renderSidebar();
        this._updateEmptyState();
        this._scheduleSave();

        // Select and focus
        this.selectNote(id);
        this.graph.focusNode(id);

        Toast.show(`Nota "${note.title}" criada!`, 'success');
        return id;
    }

    updateNote(id, updates) {
        const note = this.notes.get(id);
        if (!note) return;

        if (updates.title !== undefined && updates.title !== note.title) {
            note.title = updates.title;
            this.graph.updateNode(id, { label: note.title });
        }
        if (updates.content !== undefined) {
            note.content = updates.content;
            const r = this._noteRadius(note);
            this.graph.updateNode(id, { radius: r });
        }
        note.updatedAt = new Date().toISOString();

        // Sync position from graph
        const graphNode = this.graph.nodes.get(id);
        if (graphNode) {
            note.x = graphNode.pos.x;
            note.y = graphNode.pos.y;
        }

        this._renderSidebar();
        this._scheduleSave();
    }

    deleteNote(id) {
        const note = this.notes.get(id);
        if (!note) return;

        // Remove connections
        for (const otherId of [...note.connections]) {
            this._disconnect(id, otherId);
        }

        this.notes.delete(id);
        this.graph.removeNode(id);

        if (this.selectedNoteId === id) {
            this.selectedNoteId = null;
            this._closeEditor();
        }

        this._renderSidebar();
        this._updateEmptyState();
        this._scheduleSave();

        Toast.show(`Nota "${note.title}" deletada`, 'info');
    }

    selectNote(id) {
        const note = this.notes.get(id);
        if (!note) return;

        this.selectedNoteId = id;
        this.graph.selectedNode = id;

        this._openEditor(note);
        this._renderSidebar();
    }

    _connect(idA, idB) {
        if (idA === idB) return;
        const a = this.notes.get(idA);
        const b = this.notes.get(idB);
        if (!a || !b) return;
        if (!a.connections) a.connections = [];
        if (!b.connections) b.connections = [];
        if (!a.connections.includes(idB)) a.connections.push(idB);
        if (!b.connections.includes(idA)) b.connections.push(idA);
        this.graph.addEdge(idA, idB);
    }

    _disconnect(idA, idB) {
        const a = this.notes.get(idA);
        const b = this.notes.get(idB);
        if (a && a.connections) a.connections = a.connections.filter(c => c !== idB);
        if (b && b.connections) b.connections = b.connections.filter(c => c !== idA);
        this.graph.removeEdge(idA, idB);
    }

    _noteRadius(note) {
        const contentLen = (note.content || '').length;
        const t = clamp(contentLen / 500, 0, 1);
        return lerp(RENDER.NODE_RADIUS_MIN, RENDER.NODE_RADIUS_MAX, t);
    }

    // ── Editor Panel ──
    _openEditor(note) {
        const panel = $('#editorPanel');
        panel.classList.add('editor-open');

        $('#editorColorDot').style.backgroundColor = note.color;
        $('#editorColorDot').style.boxShadow = `0 0 8px ${note.color}60`;
        $('#editorTitle').value = note.title;
        $('#editorContent').value = note.content || '';
        $('#editorCreated').textContent = formatDate(note.createdAt);
        $('#editorUpdated').textContent = formatDate(note.updatedAt);

        this._renderEditorConnections(note);
    }

    _closeEditor() {
        const panel = $('#editorPanel');
        panel.classList.remove('editor-open');
        this.selectedNoteId = null;
        this.graph.selectedNode = null;
        this._renderSidebar();
    }

    _renderEditorConnections(note) {
        const container = $('#editorConnections');
        if (!note.connections || note.connections.length === 0) {
            container.innerHTML = '<span class="text-xs text-obs-600 italic">Nenhuma conexão</span>';
            return;
        }
        container.innerHTML = note.connections.map(connId => {
            const other = this.notes.get(connId);
            if (!other) return '';
            return `
                <span class="connection-chip" data-conn-id="${connId}">
                    <span class="w-2 h-2 rounded-full shrink-0" style="background:${other.color}"></span>
                    <span class="truncate max-w-[140px]">${other.title}</span>
                    <span class="remove-conn" data-remove-conn="${connId}" title="Remover conexão">✕</span>
                </span>
            `;
        }).join('');

        // Bind remove handlers
        container.querySelectorAll('.remove-conn').forEach(btn => {
            btn.addEventListener('click', (e) => {
                e.stopPropagation();
                const connId = btn.dataset.removeConn;
                this._disconnect(note.id, connId);
                this._renderEditorConnections(note);
                this._scheduleSave();
            });
        });
    }

    // ── Sidebar ──
    _renderSidebar(filter = '') {
        const list = $('#noteList');
        const searchTerm = filter || $('#searchInput').value.toLowerCase().trim();

        let notes = [...this.notes.values()];

        // Filter
        if (searchTerm) {
            notes = notes.filter(n =>
                n.title.toLowerCase().includes(searchTerm) ||
                (n.content && n.content.toLowerCase().includes(searchTerm))
            );
        }

        // Sort by updatedAt desc
        notes.sort((a, b) => new Date(b.updatedAt || 0) - new Date(a.updatedAt || 0));

        if (notes.length === 0 && searchTerm) {
            list.innerHTML = `
                <div class="text-center py-8">
                    <p class="text-xs text-obs-600">Nenhuma nota encontrada</p>
                </div>
            `;
        } else if (notes.length === 0) {
            list.innerHTML = '';
        } else {
            list.innerHTML = notes.map((note, i) => {
                const isActive = this.selectedNoteId === note.id;
                const preview = note.content
                    ? note.content.slice(0, 60).replace(/\n/g, ' ') + (note.content.length > 60 ? '…' : '')
                    : 'Nota vazia';
                return `
                    <div class="note-item rounded-lg px-3 py-2.5 cursor-pointer ${isActive ? 'active' : ''}"
                         data-note-id="${note.id}" style="animation-delay: ${i * 30}ms">
                        <div class="flex items-start gap-2.5">
                            <div class="w-2.5 h-2.5 rounded-full mt-1.5 shrink-0 shadow-sm" style="background:${note.color}; box-shadow: 0 0 6px ${note.color}40;"></div>
                            <div class="flex-1 min-w-0">
                                <div class="text-sm font-medium text-obs-200 truncate">${note.title}</div>
                                <div class="text-[11px] text-obs-500 truncate mt-0.5">${preview}</div>
                                <div class="text-[10px] text-obs-600 mt-1 font-mono">${formatDate(note.updatedAt)}</div>
                            </div>
                            <div class="text-[10px] text-obs-600 font-mono shrink-0 mt-1">${(note.connections || []).length}↔</div>
                        </div>
                    </div>
                `;
            }).join('');
        }

        // Update count
        $('#noteCount').textContent = this.notes.size;

        // Bind clicks
        list.querySelectorAll('.note-item').forEach(el => {
            el.addEventListener('click', () => {
                const id = el.dataset.noteId;
                this.selectNote(id);
                this.graph.focusNode(id);
            });
        });
    }

    _updateEmptyState() {
        const empty = $('#emptyState');
        if (this.notes.size === 0) {
            empty.classList.remove('hidden');
        } else {
            empty.classList.add('hidden');
        }
    }

    // ── Tooltip ──
    _updateTooltip(nodeId, sx, sy) {
        const tooltip = $('#graphTooltip');
        if (!nodeId) {
            tooltip.classList.remove('visible');
            return;
        }
        const note = this.notes.get(nodeId);
        if (!note) return;

        tooltip.querySelector('.tooltip-title').textContent = note.title;
        tooltip.querySelector('.tooltip-meta').textContent = `${(note.connections || []).length} conexões • ${formatDate(note.updatedAt)}`;
        tooltip.style.left = sx + 'px';
        tooltip.style.top = sy + 'px';
        tooltip.classList.add('visible');
    }

    // ── Persistence with Firebase ──
    _scheduleSave() {
        clearTimeout(this._saveTimer);
        this._saveTimer = setTimeout(() => this._save(), AUTOSAVE_INTERVAL);
    }

    _save() {
        // Sync positions from graph
        for (const [id, note] of this.notes) {
            const gNode = this.graph.nodes.get(id);
            if (gNode) {
                note.x = gNode.pos.x;
                note.y = gNode.pos.y;
            }
        }

        const data = {
            version: 1,
            colorIndex: this.colorIndex,
            notes: [...this.notes.values()],
        };

        const dbRef = ref(db, DB_KEY);
        set(dbRef, data).catch(e => {
            console.error('Firebase save failed:', e);
            Toast.show('Erro ao salvar no Firebase!', 'error');
        });
    }

    _listenFirebase() {
        const dbRef = ref(db, DB_KEY);
        
        onValue(dbRef, (snapshot) => {
            const data = snapshot.val();
            
            if (!data || !data.notes) {
                // If database is empty
                if (!this._isInitialLoad && this.notes.size > 0) {
                    Toast.show('Dados foram limpados remotamente', 'info');
                }
                this.notes.clear();
                this.graph.nodes.clear();
                this.graph.edges = [];
                this.colorIndex = 0;
                this._renderSidebar();
                this._updateEmptyState();
                if ($('#editorPanel').classList.contains('editor-open')) {
                    this._closeEditor();
                }
            } else {
                this._applyData(data);
                
                if (this._isInitialLoad && this.notes.size > 0) {
                    setTimeout(() => this.graph.fitAll(), 300);
                }
            }
            
            this._isInitialLoad = false;
        });
    }

    _applyData(data) {
        this.colorIndex = data.colorIndex || 0;
        
        // Track incoming notes to process deletions
        const incomingNotes = new Map();
        if (data.notes) {
            for (const n of data.notes) {
                incomingNotes.set(n.id, n);
            }
        }

        // Delete removed nodes
        for (const id of [...this.notes.keys()]) {
            if (!incomingNotes.has(id)) {
                this.notes.delete(id);
                this.graph.removeNode(id);
                if (this.selectedNoteId === id) {
                    this._closeEditor();
                }
            }
        }

        // Update or Add nodes
        for (const n of incomingNotes.values()) {
            n.connections = n.connections || [];
            
            if (this.notes.has(n.id)) {
                // Update existing
                const existing = this.notes.get(n.id);
                existing.title = n.title;
                existing.content = n.content || '';
                existing.color = n.color;
                existing.connections = n.connections;
                existing.updatedAt = n.updatedAt;
                existing.createdAt = n.createdAt;
                
                // Only sync positions if this node isn't currently being dragged
                if (this.graph.dragging !== n.id) {
                    existing.x = n.x;
                    existing.y = n.y;
                    const gNode = this.graph.nodes.get(n.id);
                    if (gNode) {
                        gNode.pos.x = n.x;
                        gNode.pos.y = n.y;
                    }
                }
                
                const radius = this._noteRadius(existing);
                this.graph.updateNode(n.id, { label: existing.title, color: existing.color, radius });
            } else {
                // Add new
                this.notes.set(n.id, n);
                const radius = this._noteRadius(n);
                this.graph.addNode(n.id, n.title, n.color, n.x, n.y, radius);
            }
        }

        // Rebuild edges
        this.graph.edges = [];
        const edgeSet = new Set();
        for (const note of this.notes.values()) {
            for (const connId of note.connections) {
                if (this.notes.has(connId)) {
                    const key = [note.id, connId].sort().join('-');
                    if (!edgeSet.has(key)) {
                        edgeSet.add(key);
                        this.graph.addEdge(note.id, connId);
                    }
                }
            }
        }

        this._renderSidebar();
        this._updateEmptyState();
        
        // Update open editor non-intrusively
        if (this.selectedNoteId && this.notes.has(this.selectedNoteId)) {
            const activeNote = this.notes.get(this.selectedNoteId);
            if ($('#editorPanel').classList.contains('editor-open')) {
                // Do not override user typing
                if (document.activeElement !== $('#editorTitle')) {
                    $('#editorTitle').value = activeNote.title;
                }
                if (document.activeElement !== $('#editorContent')) {
                    $('#editorContent').value = activeNote.content;
                }
                $('#editorColorDot').style.backgroundColor = activeNote.color;
                $('#editorColorDot').style.boxShadow = `0 0 8px ${activeNote.color}60`;
                $('#editorUpdated').textContent = formatDate(activeNote.updatedAt);
                this._renderEditorConnections(activeNote);
            }
        }
    }

    // ── Export ──
    async exportToFolder() {
        if (this.notes.size === 0) {
            Toast.show('Nenhuma nota para exportar', 'warning');
            return;
        }

        try {
            if (!('showDirectoryPicker' in window)) {
                Toast.show('Seu navegador não suporta seleção de pasta. Use o export ZIP.', 'warning');
                return;
            }
            const dirHandle = await window.showDirectoryPicker({ mode: 'readwrite' });

            for (const note of this.notes.values()) {
                const filename = sanitizeFilename(note.title) + '.md';
                const fileHandle = await dirHandle.getFileHandle(filename, { create: true });
                const writable = await fileHandle.createWritable();
                const content = this._noteToMarkdown(note);
                await writable.write(content);
                await writable.close();
            }
            Toast.show(`${this.notes.size} notas exportadas com sucesso!`, 'success');
        } catch (e) {
            if (e.name !== 'AbortError') {
                console.error('Export failed:', e);
                Toast.show('Erro ao exportar para pasta', 'error');
            }
        }
    }

    exportToJSON() {
        if (this.notes.size === 0) {
            Toast.show('Nenhuma nota para exportar', 'warning');
            return;
        }

        // Sync positions
        for (const [id, note] of this.notes) {
            const gNode = this.graph.nodes.get(id);
            if (gNode) { note.x = gNode.pos.x; note.y = gNode.pos.y; }
        }

        const data = {
            version: 1,
            exportedAt: new Date().toISOString(),
            colorIndex: this.colorIndex,
            notes: [...this.notes.values()],
        };

        const blob = new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' });
        this._download(blob, `mentalmap_backup_${this._dateSlug()}.json`);
        Toast.show('Backup JSON exportado!', 'success');
    }

    async exportToZip() {
        if (this.notes.size === 0) {
            Toast.show('Nenhuma nota para exportar', 'warning');
            return;
        }

        if (typeof JSZip === 'undefined') {
            Toast.show('JSZip não encontrado. Recarregue a página.', 'error');
            return;
        }

        const zip = new JSZip();
        const folder = zip.folder('MentalMap_Notas');

        for (const note of this.notes.values()) {
            const filename = sanitizeFilename(note.title) + '.md';
            const content = this._noteToMarkdown(note);
            folder.file(filename, content);
        }

        // Add manifest
        const manifest = {
            version: 1,
            exportedAt: new Date().toISOString(),
            noteCount: this.notes.size,
            notes: [...this.notes.values()].map(n => ({
                id: n.id,
                title: n.title,
                connections: n.connections || [],
                createdAt: n.createdAt,
                updatedAt: n.updatedAt,
            }))
        };
        folder.file('_manifest.json', JSON.stringify(manifest, null, 2));

        try {
            const blob = await zip.generateAsync({ type: 'blob' });
            this._download(blob, `mentalmap_${this._dateSlug()}.zip`);
            Toast.show('Arquivo ZIP exportado com sucesso!', 'success');
        } catch (e) {
            console.error('ZIP export failed:', e);
            Toast.show('Erro ao gerar ZIP', 'error');
        }
    }

    _noteToMarkdown(note) {
        const conns = (note.connections || [])
            .map(cid => this.notes.get(cid))
            .filter(Boolean)
            .map(n => `- [[${n.title}]]`)
            .join('\n');

        return [
            `# ${note.title}`,
            '',
            `> **Criado:** ${formatDate(note.createdAt)}`,
            `> **Última edição:** ${formatDate(note.updatedAt)}`,
            '',
            '---',
            '',
            note.content || '*Nota vazia*',
            '',
            '---',
            '',
            '## Conexões',
            '',
            conns || '*Nenhuma conexão*',
            '',
        ].join('\n');
    }

    _download(blob, filename) {
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = filename;
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        URL.revokeObjectURL(url);
    }

    _dateSlug() {
        const d = new Date();
        const pad = (n) => String(n).padStart(2, '0');
        return `${d.getFullYear()}${pad(d.getMonth() + 1)}${pad(d.getDate())}_${pad(d.getHours())}${pad(d.getMinutes())}`;
    }

    // ── Clear All ──
    clearAll() {
        // Overwrite Firebase with null to clear
        const dbRef = ref(db, DB_KEY);
        set(dbRef, null).then(() => {
            Toast.show('Todas as notas foram removidas', 'info');
        }).catch(e => {
            console.error('Failed to clear Firebase:', e);
            Toast.show('Erro ao limpar banco de dados', 'error');
        });
    }

    // ── Modals ──
    _pendingNotePos = null;

    openNewNoteModal(wx, wy) {
        this._pendingNotePos = { x: wx, y: wy };
        const input = $('#newNoteInput');
        input.value = '';
        Modal.open($('#newNoteModal'));
    }

    _confirmNewNote() {
        const input = $('#newNoteInput');
        const title = input.value.trim();
        if (!title) {
            input.focus();
            return;
        }
        Modal.close($('#newNoteModal'));
        const pos = this._pendingNotePos || {};
        this.createNote(title, pos.x, pos.y);
        this._pendingNotePos = null;
    }

    openConnectionModal() {
        if (!this.selectedNoteId) return;
        const currentNote = this.notes.get(this.selectedNoteId);
        if (!currentNote) return;

        const list = $('#connectionPickerList');
        const conns = currentNote.connections || [];
        const available = [...this.notes.values()].filter(n =>
            n.id !== this.selectedNoteId && !conns.includes(n.id)
        );

        if (available.length === 0) {
            list.innerHTML = '<p class="text-xs text-obs-600 text-center py-4">Todas as notas já estão conectadas</p>';
        } else {
            list.innerHTML = available.map(n => `
                <div class="conn-list-item flex items-center gap-3 rounded-lg" data-conn-target="${n.id}">
                    <div class="w-3 h-3 rounded-full shrink-0" style="background:${n.color}; box-shadow: 0 0 6px ${n.color}40;"></div>
                    <div class="flex-1 min-w-0">
                        <div class="text-sm text-obs-200 truncate">${n.title}</div>
                        <div class="text-[10px] text-obs-600 font-mono">${formatDate(n.updatedAt)}</div>
                    </div>
                </div>
            `).join('');

            list.querySelectorAll('.conn-list-item').forEach(el => {
                el.addEventListener('click', () => {
                    const targetId = el.dataset.connTarget;
                    this._connect(this.selectedNoteId, targetId);
                    this._renderEditorConnections(currentNote);
                    this._renderSidebar();
                    this._scheduleSave();
                    Modal.close($('#connectionModal'));
                    Toast.show('Conexão criada!', 'success');
                });
            });
        }

        Modal.open($('#connectionModal'));
    }

    openExportModal() {
        Modal.open($('#exportModal'));
    }

    openConfirmModal(title, message, onConfirm) {
        $('#confirmTitle').textContent = title;
        $('#confirmMessage').textContent = message;
        this._confirmCallback = onConfirm;
        Modal.open($('#confirmModal'));
    }

    // ── UI Event Binding ──
    _bindUI() {
        // New Note
        $('#btnNewNote').addEventListener('click', () => this.openNewNoteModal());
        $('#btnConfirmNote').addEventListener('click', () => this._confirmNewNote());
        $('#btnCancelNote').addEventListener('click', () => Modal.close($('#newNoteModal')));
        $('#newNoteOverlay').addEventListener('click', () => Modal.close($('#newNoteModal')));
        $('#newNoteInput').addEventListener('keydown', (e) => {
            if (e.key === 'Enter') this._confirmNewNote();
            if (e.key === 'Escape') Modal.close($('#newNoteModal'));
        });

        // Editor
        $('#btnCloseEditor').addEventListener('click', () => this._closeEditor());

        // Editor title change
        let titleTimer;
        $('#editorTitle').addEventListener('input', () => {
            clearTimeout(titleTimer);
            titleTimer = setTimeout(() => {
                if (!this.selectedNoteId) return;
                this.updateNote(this.selectedNoteId, { title: $('#editorTitle').value.trim() || 'Sem título' });
                const note = this.notes.get(this.selectedNoteId);
                if (note) {
                    $('#editorUpdated').textContent = formatDate(note.updatedAt);
                }
            }, 300);
        });

        // Editor content change
        let contentTimer;
        $('#editorContent').addEventListener('input', () => {
            clearTimeout(contentTimer);
            contentTimer = setTimeout(() => {
                if (!this.selectedNoteId) return;
                this.updateNote(this.selectedNoteId, { content: $('#editorContent').value });
                const note = this.notes.get(this.selectedNoteId);
                if (note) {
                    $('#editorUpdated').textContent = formatDate(note.updatedAt);
                }
            }, 300);
        });

        // Delete note
        $('#btnDeleteNote').addEventListener('click', () => {
            if (!this.selectedNoteId) return;
            const note = this.notes.get(this.selectedNoteId);
            if (!note) return;
            this.openConfirmModal(
                'Deletar Nota',
                `Tem certeza que deseja deletar "${note.title}"? Esta ação não pode ser desfeita.`,
                () => this.deleteNote(note.id)
            );
        });

        // Add Connection
        $('#btnAddConnection').addEventListener('click', () => this.openConnectionModal());
        $('#btnCancelConnection').addEventListener('click', () => Modal.close($('#connectionModal')));
        $('#connOverlay').addEventListener('click', () => Modal.close($('#connectionModal')));

        // Export
        $('#btnExport').addEventListener('click', () => this.openExportModal());
        $('#btnExportFolder').addEventListener('click', () => {
            Modal.close($('#exportModal'));
            this.exportToFolder();
        });
        $('#btnExportJSON').addEventListener('click', () => {
            Modal.close($('#exportModal'));
            this.exportToJSON();
        });
        $('#btnExportZip').addEventListener('click', () => {
            Modal.close($('#exportModal'));
            this.exportToZip();
        });
        $('#btnCancelExport').addEventListener('click', () => Modal.close($('#exportModal')));
        $('#exportOverlay').addEventListener('click', () => Modal.close($('#exportModal')));

        // Confirm modal
        $('#btnConfirmOk').addEventListener('click', () => {
            Modal.close($('#confirmModal'));
            if (this._confirmCallback) {
                this._confirmCallback();
                this._confirmCallback = null;
            }
        });
        $('#btnConfirmCancel').addEventListener('click', () => Modal.close($('#confirmModal')));
        $('#confirmOverlay').addEventListener('click', () => Modal.close($('#confirmModal')));

        // Clear All
        $('#btnClearAll').addEventListener('click', () => {
            if (this.notes.size === 0) {
                Toast.show('Nenhuma nota para limpar', 'warning');
                return;
            }
            this.openConfirmModal(
                'Limpar Tudo',
                `Tem certeza que deseja deletar TODAS as ${this.notes.size} notas? Esta ação não pode ser desfeita.`,
                () => this.clearAll()
            );
        });

        // Search
        let searchTimer;
        $('#searchInput').addEventListener('input', () => {
            clearTimeout(searchTimer);
            searchTimer = setTimeout(() => this._renderSidebar(), 150);
        });

        // Zoom controls
        $('#btnZoomIn').addEventListener('click', () => this.graph.zoomBy(0.2));
        $('#btnZoomOut').addEventListener('click', () => this.graph.zoomBy(-0.2));
        $('#btnZoomFit').addEventListener('click', () => this.graph.fitAll());

        // Mobile sidebar
        $('#btnMobileSidebar').addEventListener('click', () => {
            const sidebar = $('#sidebar');
            sidebar.classList.toggle('sidebar-open');
        });

        // Keyboard shortcuts
        document.addEventListener('keydown', (e) => {
            // Ctrl+N = New note
            if ((e.ctrlKey || e.metaKey) && e.key === 'n') {
                e.preventDefault();
                this.openNewNoteModal();
            }
            // Ctrl+E = Export
            if ((e.ctrlKey || e.metaKey) && e.key === 'e') {
                e.preventDefault();
                this.openExportModal();
            }
            // Escape = close editor / modal
            if (e.key === 'Escape') {
                if ($('#confirmModal').classList.contains('flex')) {
                    Modal.close($('#confirmModal'));
                } else if ($('#connectionModal').classList.contains('flex')) {
                    Modal.close($('#connectionModal'));
                } else if ($('#exportModal').classList.contains('flex')) {
                    Modal.close($('#exportModal'));
                } else if ($('#newNoteModal').classList.contains('flex')) {
                    Modal.close($('#newNoteModal'));
                } else if ($('#editorPanel').classList.contains('editor-open')) {
                    this._closeEditor();
                }
            }
            // Ctrl+F = focus search
            if ((e.ctrlKey || e.metaKey) && e.key === 'f') {
                // Don't prevent default if inside editor
                const active = document.activeElement;
                if (active && (active.id === 'editorContent' || active.id === 'editorTitle')) return;
                e.preventDefault();
                $('#searchInput').focus();
            }
            // Delete = delete selected note
            if (e.key === 'Delete' && this.selectedNoteId) {
                const active = document.activeElement;
                if (active && (active.tagName === 'INPUT' || active.tagName === 'TEXTAREA')) return;
                const note = this.notes.get(this.selectedNoteId);
                if (note) {
                    this.openConfirmModal(
                        'Deletar Nota',
                        `Tem certeza que deseja deletar "${note.title}"?`,
                        () => this.deleteNote(note.id)
                    );
                }
            }
        });

        // Periodic position sync (save positions)
        setInterval(() => {
            if (this.notes.size > 0) {
                let changed = false;
                for (const [id, note] of this.notes) {
                    const gNode = this.graph.nodes.get(id);
                    if (gNode) {
                        const dx = Math.abs(note.x - gNode.pos.x);
                        const dy = Math.abs(note.y - gNode.pos.y);
                        if (dx > 1 || dy > 1) {
                            note.x = gNode.pos.x;
                            note.y = gNode.pos.y;
                            changed = true;
                        }
                    }
                }
                if (changed) this._scheduleSave();
            }
        }, 5000);
    }
}


// ═══════════════════════════════════════════════════════════════
// Boot
// ═══════════════════════════════════════════════════════════════
document.addEventListener('DOMContentLoaded', () => {
    window.app = new MentalMapApp();
});
