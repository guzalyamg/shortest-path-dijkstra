"""
==============================================================================
  PROJECT  : Shortest Path Finder using Dijkstra's Algorithm
  COURSE   : Data Structures — Final Project
  LANGUAGE : Python 3 (tkinter GUI, heapq priority queue)
  MODULES  : Splash Screen, Login/Auth, Graph Canvas, Dijkstra Visualiser,
             Step-Through Mode, Distance Table, Save/Load, Exit Confirmation
==============================================================================

  HOW TO RUN:
      python shortest_path_finder.py

  DEFAULT LOGIN:
      Username: admin      Password: 1234
      Username: student    Password: dsproject
      (or register a new account from the login screen)

  CONTROLS:
      Left-click canvas   -> Add node (in Add Node mode)
      Click node + node   -> Add edge with weight (in Add Edge mode)
      Drag node           -> Move node to new position
      Right-click node    -> Context menu (Set Source / Target / Delete)
      Run Dijkstra's      -> Animated shortest path visualisation
      Step Through        -> Advance algorithm one node at a time
==============================================================================
"""

# ── Standard library imports ──────────────────────────────────────────────────
import tkinter as tk                        # Main GUI framework
from tkinter import messagebox              # Pop-up dialog boxes
from tkinter import simpledialog            # Simple input dialog
from tkinter import ttk                     # Themed widgets (Treeview table)
import heapq                                # Min-heap for priority queue
import math                                 # Distance calculations (hypot)
import json                                 # Save/Load graph as JSON
import os                                   # File path handling

# ==============================================================================
#  COLOUR PALETTE  —  Dark Neon Theme
#  All colours defined here so changing the theme is easy.
# ==============================================================================
BG          = "#0d0f1a"   # Main window background (very dark navy)
PANEL_BG    = "#12152b"   # Sidebar / info panel background
CANVAS_BG   = "#0a0c18"   # Graph canvas background
ACCENT      = "#00e5ff"   # Primary accent — cyan
ACCENT2     = "#ff6b35"   # Secondary accent — orange
NODE_DEF    = "#1e2a4a"   # Default (unvisited) node fill
NODE_BORDER = "#3a4a7a"   # Default node border colour
NODE_START  = "#00e5ff"   # Source node colour (cyan)
NODE_END    = "#ff6b35"   # Target node colour (orange)
NODE_VISIT  = "#ffd700"   # Visited / finalised node (gold)
NODE_PATH   = "#00ff88"   # Final shortest-path node (green)
EDGE_DEF    = "#2a3a5a"   # Default edge colour
EDGE_PATH   = "#00ff88"   # Edge on shortest path (green)
TEXT_MAIN   = "#e8eeff"   # Main text colour
TEXT_DIM    = "#5a6a9a"   # Dimmed / secondary text
TEXT_BRIGHT = "#ffffff"   # Bright white text
BTN_BG      = "#1a2040"   # Button background
BTN_HOVER   = "#253060"   # Button hover colour

# Visual constants
NODE_R     = 22    # Radius of each node circle (pixels)
ANIM_DELAY = 450   # Milliseconds between animation frames

# ==============================================================================
#  GRAPH DATA STRUCTURE
#  Represents a weighted, undirected graph using an adjacency list.
#  An adjacency list uses a dictionary of dictionaries:
#      edges[u][v] = weight   means there is an edge from u to v with that weight
#  This is more space-efficient than a matrix for sparse graphs: O(V + E) space.
# ==============================================================================
class Graph:
    """
    Weighted undirected graph implemented with an adjacency list.

    Attributes:
        nodes (dict): Maps node_id -> (x, y) canvas coordinates
        edges (dict): Adjacency list — edges[u][v] = weight
    """

    def __init__(self):
        # Dictionary: node_id -> (x, y) pixel position on canvas
        self.nodes = {}
        # Adjacency list: edges[node_id] = {neighbour: weight, ...}
        self.edges = {}

    def add_node(self, node_id, x, y):
        """
        Add a new node to the graph at canvas position (x, y).
        If the node already exists its position is updated.
        """
        self.nodes[node_id] = (x, y)
        # Initialise an empty neighbour dict if this is a new node
        if node_id not in self.edges:
            self.edges[node_id] = {}

    def remove_node(self, node_id):
        """
        Remove a node and ALL edges connected to it.
        We must clean up both directions in the adjacency list.
        """
        if node_id not in self.nodes:
            return
        del self.nodes[node_id]
        del self.edges[node_id]
        # Remove this node from every other node's neighbour list
        for neighbour_dict in self.edges.values():
            neighbour_dict.pop(node_id, None)

    def add_edge(self, u, v, weight):
        """
        Add an undirected weighted edge between nodes u and v.
        We store both directions because the graph is undirected:
            edges[u][v] = weight  AND  edges[v][u] = weight
        """
        if u not in self.nodes or v not in self.nodes:
            return   # Both endpoints must exist
        self.edges[u][v] = weight
        self.edges[v][u] = weight   # Undirected: add reverse direction too

    def remove_edge(self, u, v):
        """Remove the undirected edge between u and v (both directions)."""
        self.edges[u].pop(v, None)
        self.edges[v].pop(u, None)

    def dijkstra(self, source, target):
        """
        Dijkstra's Shortest Path Algorithm using a min-heap priority queue.

        ALGORITHM STEPS:
        1. Initialise dist[source] = 0, dist[all others] = infinity.
        2. Push (0, source) into the min-heap.
        3. Pop the node u with the smallest tentative distance.
        4. If u is already finalised (visited), skip it.
        5. Mark u as finalised. For each unvisited neighbour v of u:
               new_dist = dist[u] + weight(u, v)
               If new_dist < dist[v]:  update dist[v], record parent[v] = u,
                                       push (new_dist, v) to heap.
        6. Stop early if u == target (its distance is now optimal).
        7. Reconstruct path by following parent pointers from target to source.

        TIME COMPLEXITY:  O((V + E) log V)  using a binary min-heap
        SPACE COMPLEXITY: O(V + E)

        Args:
            source (str): Starting node ID
            target (str): Destination node ID

        Returns:
            dist          (dict): Shortest distance from source to every node
            parent        (dict): Predecessor of each node on the shortest path
            visited_order (list): Nodes in the order they were finalised
            path          (list): Reconstructed shortest path [source, ..., target]
                                  Empty list if no path exists.
        """
        INF = float('inf')

        # Step 1: Initialise all distances to infinity, source to 0
        dist   = {node: INF  for node in self.nodes}
        parent = {node: None for node in self.nodes}
        dist[source] = 0

        # Min-heap stores tuples: (tentative_distance, node_id)
        # heapq in Python is a min-heap, so the smallest distance is always at index 0
        heap = [(0, source)]

        visited      = set()   # Set of finalised nodes (their distance won't change)
        visited_order = []     # Track the order nodes are finalised (for animation)

        # Step 3–6: Main relaxation loop
        while heap:
            d, u = heapq.heappop(heap)   # Extract node with smallest distance

            # Skip if this node was already finalised (stale heap entry)
            if u in visited:
                continue

            visited.add(u)           # Mark as finalised
            visited_order.append(u)  # Record visit order for animation

            # Early exit: once the target is finalised, its distance is optimal
            if u == target:
                break

            # Step 5: Relax edges from u to each unvisited neighbour
            for v, w in self.edges[u].items():
                if v not in visited:
                    new_dist = d + w                # Candidate distance via u
                    if new_dist < dist[v]:          # Found a shorter path to v
                        dist[v]   = new_dist
                        parent[v] = u               # Remember we came from u
                        heapq.heappush(heap, (new_dist, v))

        # Step 7: Reconstruct path by following parent pointers backwards
        path = []
        cur  = target
        while cur is not None:
            path.append(cur)
            cur = parent[cur]
        path.reverse()   # Reverse to get source -> target order

        # Validate: if path doesn't start at source, no path exists
        if not path or path[0] != source:
            path = []

        return dist, parent, visited_order, path

    def edge_count(self):
        """Return the number of undirected edges (divide by 2 since stored twice)."""
        return sum(len(v) for v in self.edges.values()) // 2

    def clear(self):
        """Remove all nodes and edges from the graph."""
        self.nodes.clear()
        self.edges.clear()

    def to_dict(self):
        """Serialise graph to a plain dict (for JSON saving)."""
        return {"nodes": self.nodes, "edges": self.edges}

    def from_dict(self, data):
        """Reconstruct graph from a dict loaded from JSON."""
        # Convert node positions back to tuples (JSON stores them as lists)
        self.nodes = {k: tuple(v) for k, v in data["nodes"].items()}
        self.edges = data["edges"]


# ==============================================================================
#  SPLASH SCREEN
#  Shown once when the program starts. Displays title and animated progress bar.
#  Uses tkinter's after() timer to animate without blocking the event loop.
# ==============================================================================
class SplashScreen(tk.Toplevel):
    """
    Animated introduction screen shown before login.
    Automatically closes after ~2.5 seconds and calls on_done callback.
    """

    def __init__(self, parent, on_done):
        super().__init__(parent)
        self.on_done = on_done   # Function to call when splash finishes

        # Remove the OS window border for a cleaner look
        self.overrideredirect(True)
        # Safety: if somehow the window is closed externally, call on_done
        self.protocol("WM_DELETE_WINDOW", self._finish)

        # Centre the splash window on screen
        W, H = 600, 380
        sw = self.winfo_screenwidth()
        sh = self.winfo_screenheight()
        self.geometry(f"{W}x{H}+{(sw-W)//2}+{(sh-H)//2}")
        self.configure(bg=BG)

        # Cyan border frame (acts as a glowing outline)
        border = tk.Frame(self, bg=ACCENT, bd=2)
        border.place(x=0, y=0, width=W, height=H)
        inner = tk.Frame(border, bg=BG)
        inner.place(x=2, y=2, width=W-4, height=H-4)

        # Title labels
        tk.Label(inner, text="◈",
                 font=("Courier New", 36), fg=ACCENT, bg=BG).pack(pady=(40, 0))
        tk.Label(inner, text="SHORTEST PATH FINDER",
                 font=("Courier New", 22, "bold"), fg=TEXT_BRIGHT, bg=BG).pack()
        tk.Label(inner, text="Dijkstra's Algorithm Visualizer",
                 font=("Courier New", 11), fg=ACCENT, bg=BG).pack(pady=4)
        tk.Frame(inner, bg=ACCENT, height=1).pack(fill="x", padx=60, pady=12)
        tk.Label(inner, text="Data Structures — Final Project",
                 font=("Courier New", 10), fg=TEXT_DIM, bg=BG).pack()
        tk.Label(inner, text="Python  •  tkinter  •  heapq",
                 font=("Courier New", 9), fg=TEXT_DIM, bg=BG).pack(pady=2)

        # Progress bar: grey background + cyan foreground that grows
        self.bar_frame = tk.Frame(inner, bg=NODE_BORDER, height=6, width=360)
        self.bar_frame.pack(pady=24)
        self.bar = tk.Frame(self.bar_frame, bg=ACCENT, height=6, width=0)
        self.bar.place(x=0, y=0)

        # Status text below progress bar
        self.status = tk.Label(inner, text="Initialising...",
                               font=("Courier New", 9), fg=TEXT_DIM, bg=BG)
        self.status.pack()

        # Animation steps: (bar_width, status_message)
        self._step = 0
        self._steps = [
            (80,  "Loading graph engine..."),
            (160, "Building priority queue..."),
            (260, "Initialising canvas..."),
            (360, "Ready!"),
        ]
        self.after(300, self._animate)   # Start animation after 300ms

    def _animate(self):
        """Advance the progress bar one step at a time using after() callbacks."""
        if self._step < len(self._steps):
            width, msg = self._steps[self._step]
            self.bar.configure(width=width)
            self.status.configure(text=msg)
            self._step += 1
            delay = 500 if self._step < len(self._steps) else 700
            self.after(delay, self._animate)
        else:
            self.after(300, self._finish)

    def _finish(self):
        """Close splash and trigger the next step (login)."""
        self.destroy()
        self.on_done()


# ==============================================================================
#  USER AUTHENTICATION
#  Simple file-based login. Credentials stored in users.json as plain text.
#  In a real system we would hash passwords (e.g. with hashlib or bcrypt).
# ==============================================================================

# Path to credentials file (same directory as this script)
USERS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "users.json")

def load_users():
    """Load user credentials from JSON file. Returns defaults if file missing."""
    if os.path.exists(USERS_FILE):
        with open(USERS_FILE, "r") as f:
            return json.load(f)
    # Default accounts if no file exists yet
    return {"admin": "1234", "student": "dsproject"}

def save_users(users):
    """Persist user credentials to JSON file."""
    with open(USERS_FILE, "w") as f:
        json.dump(users, f, indent=2)


class LoginScreen(tk.Toplevel):
    """
    Login / Registration window.
    Shown after the splash screen. Blocks access until valid credentials entered.
    """

    def __init__(self, parent, on_success):
        super().__init__(parent)
        self.on_success = on_success   # Callback when login succeeds
        self.users = load_users()      # Load existing credentials

        self.title("Login")
        self.resizable(False, False)
        self.configure(bg=BG)

        # Explicitly handle the window X button so tkinter doesn't crash
        self.protocol("WM_DELETE_WINDOW", self.destroy)

        # Centre window on screen
        W, H = 420, 490
        sw = self.winfo_screenwidth()
        sh = self.winfo_screenheight()
        self.geometry(f"{W}x{H}+{(sw-W)//2}+{(sh-H)//2}")

        self.grab_set()   # Make this window modal (must come after geometry)

        # Card container with cyan border
        card = tk.Frame(self, bg=PANEL_BG,
                        highlightbackground=ACCENT, highlightthickness=1)
        card.place(x=30, y=30, width=W-60, height=H-60)

        # Title
        tk.Label(card, text="◈ LOGIN",
                 font=("Courier New", 18, "bold"), fg=ACCENT,
                 bg=PANEL_BG).pack(pady=(36, 4))
        tk.Label(card, text="Shortest Path Finder",
                 font=("Courier New", 10), fg=TEXT_DIM,
                 bg=PANEL_BG).pack()
        tk.Frame(card, bg=NODE_BORDER, height=1).pack(fill="x", padx=30, pady=20)

        # Username field
        tk.Label(card, text="USERNAME",
                 font=("Courier New", 8, "bold"), fg=TEXT_DIM,
                 bg=PANEL_BG).pack(anchor="w", padx=40)
        self.user_var = tk.StringVar()
        user_entry = tk.Entry(card, textvariable=self.user_var,
                              font=("Courier New", 12), bg=NODE_DEF,
                              fg=TEXT_BRIGHT, insertbackground=ACCENT,
                              relief="flat", bd=0)
        user_entry.pack(fill="x", padx=40, ipady=8)
        tk.Frame(card, bg=ACCENT, height=1).pack(fill="x", padx=40)
        tk.Label(card, bg=PANEL_BG).pack(pady=4)   # Spacer

        # Password field
        tk.Label(card, text="PASSWORD",
                 font=("Courier New", 8, "bold"), fg=TEXT_DIM,
                 bg=PANEL_BG).pack(anchor="w", padx=40)
        self.pass_var = tk.StringVar()
        self.pass_entry = tk.Entry(card, textvariable=self.pass_var,
                                   font=("Courier New", 12), bg=NODE_DEF,
                                   fg=TEXT_BRIGHT, insertbackground=ACCENT,
                                   relief="flat", bd=0, show="●")
        self.pass_entry.pack(fill="x", padx=40, ipady=8)
        tk.Frame(card, bg=ACCENT, height=1).pack(fill="x", padx=40)

        # Show/hide password toggle
        self.show_pass = tk.BooleanVar()
        tk.Checkbutton(card, text="Show password",
                       variable=self.show_pass,
                       command=self._toggle_pass,
                       font=("Courier New", 8), fg=TEXT_DIM, bg=PANEL_BG,
                       selectcolor=NODE_DEF, activebackground=PANEL_BG,
                       activeforeground=TEXT_DIM).pack(anchor="w", padx=40, pady=6)

        # Error/success message label
        self.msg = tk.Label(card, text="",
                            font=("Courier New", 9), fg="#ff4466", bg=PANEL_BG)
        self.msg.pack()

        # Action buttons
        self._make_btn(card, "LOGIN",    self._login,        ACCENT)
        self._make_btn(card, "REGISTER", self._save_new_user, ACCENT2)
        self._make_btn(card, "EXIT",     self.destroy,        TEXT_DIM)

        user_entry.focus()
        self.bind("<Return>", lambda e: self._login())   # Enter key triggers login

    def _make_btn(self, parent, text, cmd, fg):
        """Helper: create a styled full-width button."""
        f = tk.Frame(parent, bg=PANEL_BG)
        f.pack(fill="x", padx=40, pady=3)
        tk.Button(f, text=text, font=("Courier New", 10, "bold"),
                  fg=fg, bg=BTN_BG, relief="flat", bd=0,
                  activebackground=BTN_HOVER, activeforeground=fg,
                  cursor="hand2", command=cmd).pack(fill="x", ipady=8)

    def _toggle_pass(self):
        """Show or hide password characters based on checkbox state."""
        self.pass_entry.config(show="" if self.show_pass.get() else "●")

    def _login(self):
        """Validate credentials. On success, close window and call on_success."""
        u = self.user_var.get().strip()
        p = self.pass_var.get().strip()
        if u in self.users and self.users[u] == p:
            self.grab_release()
            self.destroy()
            self.on_success()   # Open main application
        else:
            self.msg.config(fg="#ff4466", text="✗  Invalid username or password")

    def _save_new_user(self):
        """Register a new user account and save to file."""
        u = self.user_var.get().strip()
        p = self.pass_var.get().strip()
        if not u or not p:
            self.msg.config(fg="#ff4466", text="✗  Enter a username and password first")
        elif u in self.users:
            self.msg.config(fg="#ff4466", text="✗  Username already exists")
        else:
            self.users[u] = p
            save_users(self.users)
            self.msg.config(fg="#00ff88", text="✓  Registered! You can now login.")


# ==============================================================================
#  MAIN APPLICATION
#  Handles: layout, canvas drawing, mouse interaction, algorithm animation.
# ==============================================================================
class App(tk.Tk):
    """
    Main application window.
    Orchestrates the splash screen, login, and graph visualisation interface.
    """

    def __init__(self):
        super().__init__()
        self.withdraw()   # Hide root window until login completes

        # ── Core data ─────────────────────────────────────────────
        self.graph        = Graph()   # The graph data structure
        self.node_counter = 0         # Auto-increments to label nodes A, B, C ...
        self.start_node   = None      # Currently selected source node
        self.end_node     = None      # Currently selected target node
        self._final_path  = []        # Stores the last computed shortest path

        # ── Interaction state ─────────────────────────────────────
        # mode controls what happens when user clicks the canvas
        self.mode      = "add_node"   # Modes: add_node | add_edge | delete |
                                      #        select_start | select_end
        self.edge_first = None        # First node selected when adding an edge
        self.dragging   = None        # Node being dragged (if any)

        # ── Animation state ───────────────────────────────────────
        self.anim_running = False     # True while auto-animation is playing
        self.anim_dist    = {}        # Distance dict from last algorithm run

        # Start the splash screen after the event loop begins
        self.after(100, self._show_splash)

    # ── Startup flow ──────────────────────────────────────────────────────────

    def _show_splash(self):
        """Show the animated splash screen, then proceed to login."""
        splash = SplashScreen(self, self._show_login)
        self.wait_window(splash)

    def _show_login(self):
        """Show the login window. After success, build the main UI."""
        login = LoginScreen(self, self._build_main_ui)
        self.wait_window(login)

    def _build_main_ui(self):
        """Build and display the main application window after successful login."""
        self.title("Shortest Path Finder — Dijkstra's Algorithm")
        self.configure(bg=BG)
        self.deiconify()   # Show the root window

        # Maximise window — try different methods for cross-platform compatibility
        try:
            self.state("zoomed")          # Works on Windows
        except Exception:
            try:
                self.attributes("-zoomed", True)   # Works on Linux
            except Exception:
                self.geometry("1200x750")  # Fallback fixed size

        self._build_layout()
        self._bind_canvas()
        self._update_status("Welcome! Click canvas to add nodes. "
                            "Use sidebar buttons to change mode.")

    # ── Layout construction ───────────────────────────────────────────────────

    def _build_layout(self):
        """Create the three-column layout: sidebar | canvas | info panel."""
        # Left sidebar — operation buttons
        self.sidebar = tk.Frame(self, bg=PANEL_BG, width=225)
        self.sidebar.pack(side="left", fill="y")
        self.sidebar.pack_propagate(False)   # Prevent sidebar from shrinking

        # Centre — graph canvas (expands to fill remaining space)
        self.canvas = tk.Canvas(self, bg=CANVAS_BG,
                                highlightthickness=0, cursor="crosshair")
        self.canvas.pack(side="left", fill="both", expand=True)

        # Right — algorithm info and distance table
        self.info_panel = tk.Frame(self, bg=PANEL_BG, width=265)
        self.info_panel.pack(side="right", fill="y")
        self.info_panel.pack_propagate(False)

        self._build_sidebar()
        self._build_info_panel()

    def _section_label(self, parent, text):
        """Add a divider and section heading to the sidebar."""
        tk.Frame(parent, bg=NODE_BORDER, height=1).pack(
            fill="x", padx=16, pady=(12, 0))
        if text:
            tk.Label(parent, text=text,
                     font=("Courier New", 8, "bold"), fg=TEXT_DIM,
                     bg=PANEL_BG).pack(anchor="w", padx=16, pady=(4, 0))

    def _sidebar_btn(self, parent, text, cmd, fg=TEXT_MAIN):
        """Create a full-width styled sidebar button and return the widget."""
        f = tk.Frame(parent, bg=PANEL_BG)
        f.pack(fill="x", padx=12, pady=2)
        btn = tk.Button(f, text=text,
                        font=("Courier New", 9, "bold"),
                        fg=fg, bg=BTN_BG, relief="flat", bd=0,
                        activebackground=BTN_HOVER, activeforeground=fg,
                        cursor="hand2", command=cmd, anchor="w", padx=10)
        btn.pack(fill="x", ipady=7)
        return btn

    def _build_sidebar(self):
        """Populate the left sidebar with all operation buttons."""
        sb = self.sidebar

        # Title
        tk.Label(sb, text="◈ PATH FINDER",
                 font=("Courier New", 13, "bold"), fg=ACCENT,
                 bg=PANEL_BG).pack(pady=(24, 0))
        tk.Label(sb, text="Dijkstra's Algorithm",
                 font=("Courier New", 8), fg=TEXT_DIM, bg=PANEL_BG).pack(pady=(0,8))

        # Graph building buttons
        self._section_label(sb, "GRAPH OPERATIONS")
        self._sidebar_btn(sb, "⊕  Add Node",
                          lambda: self._set_mode("add_node"), ACCENT)
        # Store this button so Step-Through mode can relabel it
        self.btn_add_edge = self._sidebar_btn(
            sb, "⟷  Add Edge", lambda: self._set_mode("add_edge"))
        self._sidebar_btn(sb, "◎  Set Source",
                          lambda: self._set_mode("select_start"), NODE_START)
        self._sidebar_btn(sb, "◎  Set Target",
                          lambda: self._set_mode("select_end"), NODE_END)
        self._sidebar_btn(sb, "✕  Delete Node/Edge",
                          lambda: self._set_mode("delete"), "#ff4466")

        # Algorithm buttons
        self._section_label(sb, "ALGORITHM")
        self._sidebar_btn(sb, "▶  Run Dijkstra's",
                          self._run_dijkstra, NODE_PATH)
        self._sidebar_btn(sb, "◼  Step Through",
                          self._step_through)
        self._sidebar_btn(sb, "↺  Reset View",
                          self._reset_view)

        # Graph file buttons
        self._section_label(sb, "GRAPH")
        self._sidebar_btn(sb, "⊞  Load Example",  self._load_example)
        self._sidebar_btn(sb, "▣  Save Graph",    self._save_graph)
        self._sidebar_btn(sb, "▤  Load Graph",    self._load_graph_file)
        self._sidebar_btn(sb, "⌫  Clear All",
                          self._clear_all, "#ff6b35")

        # Exit
        self._section_label(sb, "")
        self._sidebar_btn(sb, "⏻  Exit", self._exit, TEXT_DIM)

        # Current mode label pinned to bottom of sidebar
        tk.Frame(sb, bg=NODE_BORDER, height=1).pack(
            fill="x", padx=16, side="bottom", pady=4)
        self.mode_label = tk.Label(sb, text="MODE: ADD NODE",
                                   font=("Courier New", 8, "bold"),
                                   fg=ACCENT, bg=PANEL_BG)
        self.mode_label.pack(side="bottom", pady=4)

    def _build_info_panel(self):
        """Build the right info panel with result labels, legend, and distance table."""
        ip = self.info_panel

        # Section heading
        tk.Label(ip, text="ALGORITHM INFO",
                 font=("Courier New", 10, "bold"), fg=ACCENT,
                 bg=PANEL_BG).pack(pady=(24, 4))
        tk.Frame(ip, bg=NODE_BORDER, height=1).pack(fill="x", padx=16)

        # Key result labels (Source, Target, Distance, Path, Node count, Edge count)
        self.lbl_source = self._info_row(ip, "Source :", "—")
        self.lbl_target = self._info_row(ip, "Target :", "—")
        self.lbl_dist   = self._info_row(ip, "Distance:", "—")
        self.lbl_path   = self._info_row(ip, "Path    :", "—")
        self.lbl_nodes  = self._info_row(ip, "Nodes   :", "0")
        self.lbl_edges  = self._info_row(ip, "Edges   :", "0")

        tk.Frame(ip, bg=NODE_BORDER, height=1).pack(fill="x", padx=16, pady=8)

        # Colour legend
        tk.Label(ip, text="LEGEND",
                 font=("Courier New", 9, "bold"), fg=TEXT_DIM,
                 bg=PANEL_BG).pack(anchor="w", padx=16)
        self._legend(ip, NODE_START, "Source node")
        self._legend(ip, NODE_END,   "Target node")
        self._legend(ip, NODE_VISIT, "Visited (finalised)")
        self._legend(ip, NODE_PATH,  "Shortest path")
        self._legend(ip, NODE_DEF,   "Unvisited node")

        tk.Frame(ip, bg=NODE_BORDER, height=1).pack(fill="x", padx=16, pady=8)

        # Distance table heading
        tk.Label(ip, text="DISTANCE TABLE",
                 font=("Courier New", 9, "bold"), fg=TEXT_DIM,
                 bg=PANEL_BG).pack(anchor="w", padx=16)

        # Treeview table — shows dist from source to every node after algorithm runs
        frame = tk.Frame(ip, bg=PANEL_BG)
        frame.pack(fill="both", expand=True, padx=8, pady=4)

        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Dark.Treeview",
                        background=NODE_DEF, fieldbackground=NODE_DEF,
                        foreground=TEXT_MAIN, rowheight=22,
                        font=("Courier New", 9))
        style.configure("Dark.Treeview.Heading",
                        background=BTN_BG, foreground=ACCENT,
                        font=("Courier New", 8, "bold"))
        style.map("Dark.Treeview", background=[("selected", BTN_HOVER)])

        self.dist_table = ttk.Treeview(frame,
                                        columns=("node", "dist"),
                                        show="headings",
                                        style="Dark.Treeview",
                                        height=14)
        self.dist_table.heading("node", text="Node")
        self.dist_table.heading("dist", text="Shortest Dist")
        self.dist_table.column("node", width=80,  anchor="center")
        self.dist_table.column("dist", width=120, anchor="center")

        sb2 = ttk.Scrollbar(frame, orient="vertical",
                             command=self.dist_table.yview)
        self.dist_table.configure(yscrollcommand=sb2.set)
        self.dist_table.pack(side="left", fill="both", expand=True)
        sb2.pack(side="right", fill="y")

        # Status bar at bottom of info panel
        self.status_var = tk.StringVar(value="Ready")
        tk.Label(ip, textvariable=self.status_var,
                 font=("Courier New", 8), fg=TEXT_DIM, bg=PANEL_BG,
                 wraplength=245, justify="left").pack(
            side="bottom", pady=8, padx=8)

    def _info_row(self, parent, label, value):
        """Create a key-value label pair in the info panel. Returns the StringVar."""
        f = tk.Frame(parent, bg=PANEL_BG)
        f.pack(fill="x", padx=16, pady=2)
        tk.Label(f, text=label, font=("Courier New", 8), fg=TEXT_DIM,
                 bg=PANEL_BG, width=9, anchor="w").pack(side="left")
        var = tk.StringVar(value=value)
        tk.Label(f, textvariable=var, font=("Courier New", 9, "bold"),
                 fg=TEXT_MAIN, bg=PANEL_BG, anchor="w").pack(side="left")
        return var

    def _legend(self, parent, color, text):
        """Add one coloured-circle + label legend entry."""
        f = tk.Frame(parent, bg=PANEL_BG)
        f.pack(fill="x", padx=16, pady=1)
        # Draw a small filled circle as the colour sample
        c = tk.Canvas(f, width=14, height=14, bg=PANEL_BG, highlightthickness=0)
        c.pack(side="left")
        c.create_oval(1, 1, 13, 13, fill=color, outline="")
        tk.Label(f, text=text, font=("Courier New", 8), fg=TEXT_DIM,
                 bg=PANEL_BG).pack(side="left", padx=6)

    # ── Canvas mouse bindings ─────────────────────────────────────────────────

    def _bind_canvas(self):
        """Attach mouse event handlers to the canvas."""
        self.canvas.bind("<Button-1>",        self._on_click)     # Left click
        self.canvas.bind("<B1-Motion>",       self._on_drag)      # Click + drag
        self.canvas.bind("<ButtonRelease-1>", self._on_release)   # Release
        self.canvas.bind("<Button-3>",        self._on_right_click)  # Right click
        self.canvas.bind("<Configure>",
                         lambda e: self._redraw())   # Redraw on resize

    # ── Mode management ───────────────────────────────────────────────────────

    def _set_mode(self, mode):
        """Switch the current interaction mode and update the mode label."""
        self.mode = mode
        self.edge_first = None   # Reset partial edge selection

        labels = {
            "add_node":     "ADD NODE",
            "add_edge":     "ADD EDGE",
            "delete":       "DELETE",
            "select_start": "SET SOURCE",
            "select_end":   "SET TARGET",
        }
        self.mode_label.config(text=f"MODE: {labels.get(mode, mode.upper())}")

        hints = {
            "add_node":     "Click empty canvas space to place a node.",
            "add_edge":     "Click two nodes to connect with a weighted edge.",
            "delete":       "Click a node or edge midpoint to delete it.",
            "select_start": "Click a node to set it as the source.",
            "select_end":   "Click a node to set it as the target.",
        }
        self._update_status(hints.get(mode, ""))

    # ── Mouse event handlers ──────────────────────────────────────────────────

    def _on_click(self, event):
        """Handle left mouse button click on the canvas based on current mode."""
        if self.anim_running:
            return   # Ignore clicks during animation

        x, y = event.x, event.y
        hit  = self._node_at(x, y)   # Check if click lands on an existing node

        if self.mode == "add_node":
            # Only add a node if click is on empty space (not on an existing node)
            if hit is None:
                self._add_node(x, y)

        elif self.mode == "add_edge":
            if hit:
                if self.edge_first is None:
                    # First click: remember the starting node
                    self.edge_first = hit
                    self._update_status(f"Node {hit} selected. Now click second node.")
                    self._redraw()   # Highlight selected node
                elif hit != self.edge_first:
                    # Second click on a different node: ask for weight and add edge
                    self._ask_weight(self.edge_first, hit)
                    self.edge_first = None
                    self._redraw()
                else:
                    # Clicked the same node twice: cancel selection
                    self.edge_first = None
                    self._update_status("Cancelled. Click a different node.")
                    self._redraw()

        elif self.mode == "delete":
            if hit:
                # Delete the clicked node (and all its connected edges)
                self.graph.remove_node(hit)
                if self.start_node == hit: self.start_node = None
                if self.end_node   == hit: self.end_node   = None
                self._update_graph_info()
                self._redraw()
                self._update_status(f"Node {hit} deleted.")
            else:
                # Try to delete an edge if click is near an edge midpoint
                edge = self._edge_at(x, y)
                if edge:
                    self.graph.remove_edge(*edge)
                    self._update_graph_info()
                    self._redraw()
                    self._update_status(f"Edge {edge[0]}—{edge[1]} deleted.")

        elif self.mode == "select_start":
            if hit:
                self.start_node = hit
                self.lbl_source.set(hit)
                self._update_status(f"Source set to node '{hit}'.")
                self._redraw()

        elif self.mode == "select_end":
            if hit:
                self.end_node = hit
                self.lbl_target.set(hit)
                self._update_status(f"Target set to node '{hit}'.")
                self._redraw()

    def _on_drag(self, event):
        """Allow dragging a node to reposition it on the canvas."""
        # Start a drag if user clicks on a node in add_node mode
        if self.mode == "add_node" and self.dragging is None:
            hit = self._node_at(event.x, event.y)
            if hit:
                self.dragging = hit

        # Update node position and redraw every frame of the drag
        if self.dragging:
            self.graph.nodes[self.dragging] = (event.x, event.y)
            self._redraw()

    def _on_release(self, event):
        """End a drag operation when the mouse button is released."""
        self.dragging = None

    def _on_right_click(self, event):
        """Show a context menu on right-click over a node."""
        hit = self._node_at(event.x, event.y)
        if not hit:
            return
        menu = tk.Menu(self, tearoff=0, bg=PANEL_BG, fg=TEXT_MAIN,
                       activebackground=BTN_HOVER, activeforeground=TEXT_BRIGHT)
        menu.add_command(label=f"  Node: {hit}", state="disabled")
        menu.add_separator()
        menu.add_command(label="  Set as Source",
                         command=lambda: self._quick_set_start(hit))
        menu.add_command(label="  Set as Target",
                         command=lambda: self._quick_set_end(hit))
        menu.add_command(label="  Delete Node",
                         command=lambda: self._quick_delete(hit))
        menu.post(event.x_root, event.y_root)

    def _quick_set_start(self, n):
        self.start_node = n; self.lbl_source.set(n); self._redraw()

    def _quick_set_end(self, n):
        self.end_node = n; self.lbl_target.set(n); self._redraw()

    def _quick_delete(self, n):
        self.graph.remove_node(n)
        if self.start_node == n: self.start_node = None
        if self.end_node   == n: self.end_node   = None
        self._update_graph_info(); self._redraw()

    # ── Geometry helpers ──────────────────────────────────────────────────────

    def _node_at(self, x, y):
        """
        Return the ID of the node whose circle contains point (x, y),
        or None if no node is at that location.
        Uses Euclidean distance: sqrt((x-nx)^2 + (y-ny)^2) <= radius
        """
        for nid, (nx, ny) in self.graph.nodes.items():
            if math.hypot(x - nx, y - ny) <= NODE_R + 4:   # +4 px tolerance
                return nid
        return None

    def _edge_at(self, x, y, threshold=8):
        """
        Return the (u, v) tuple of the edge closest to point (x, y),
        or None if no edge is within threshold pixels.
        Uses perpendicular distance from point to line segment.
        """
        for u, neighbours in self.graph.edges.items():
            for v in neighbours:
                if u >= v:
                    continue   # Each undirected edge stored twice; process once
                x1, y1 = self.graph.nodes[u]
                x2, y2 = self.graph.nodes[v]
                dx, dy = x2 - x1, y2 - y1
                if dx == 0 and dy == 0:
                    continue
                # Parameter t: projection of (x,y) onto the segment [0,1]
                t = ((x - x1)*dx + (y - y1)*dy) / (dx*dx + dy*dy)
                t = max(0.0, min(1.0, t))          # Clamp to segment
                px = x1 + t*dx                      # Closest point on segment
                py = y1 + t*dy
                if math.hypot(x - px, y - py) < threshold:
                    return (u, v)
        return None

    # ── Graph modification helpers ────────────────────────────────────────────

    def _add_node(self, x, y):
        """Add a new auto-labelled node at canvas position (x, y)."""
        # Label nodes A-Z, then 26, 27, ... for more than 26 nodes
        if self.node_counter < 26:
            nid = chr(ord('A') + self.node_counter)
        else:
            nid = str(self.node_counter)
        self.node_counter += 1
        self.graph.add_node(nid, x, y)
        self._update_graph_info()
        self._redraw()
        self._update_status(f"Node '{nid}' added.")

    def _ask_weight(self, u, v):
        """Open a dialog to get the edge weight from the user, then add the edge."""
        w = simpledialog.askinteger(
            "Edge Weight",
            f"Enter weight for edge  {u} — {v}  (positive integer):",
            minvalue=1, maxvalue=9999, parent=self)
        if w is not None:
            self.graph.add_edge(u, v, w)
            self._update_graph_info()
            self._redraw()
            self._update_status(f"Edge {u}—{v} added (weight = {w}).")

    def _update_graph_info(self):
        """Refresh the node count and edge count labels in the info panel."""
        self.lbl_nodes.set(str(len(self.graph.nodes)))
        self.lbl_edges.set(str(self.graph.edge_count()))

    def _update_status(self, msg):
        """Update the status bar text at the bottom of the info panel."""
        self.status_var.set(msg)

    # ── Canvas drawing ────────────────────────────────────────────────────────

    def _redraw(self, visited=None, path=None, current=None, dist=None):
        """
        Clear and redraw the entire graph on the canvas.

        Args:
            visited  : set of node IDs that have been finalised by the algorithm
            path     : unused (path determined from self._final_path)
            current  : node ID currently being processed (highlighted differently)
            dist     : dict of distances to display above nodes
        """
        c = self.canvas
        c.delete("all")   # Clear the canvas completely

        visited    = visited or set()
        final_path = self._final_path or []

        # Compute which edges belong to the final shortest path
        path_edges = set()
        for i in range(len(final_path) - 1):
            a, b = final_path[i], final_path[i+1]
            path_edges.add((min(a, b), max(a, b)))

        # ── Draw edges first (so nodes appear on top) ──────────────
        for u, neighbours in self.graph.edges.items():
            for v, w in neighbours.items():
                if u >= v:
                    continue   # Process each undirected edge only once

                x1, y1 = self.graph.nodes[u]
                x2, y2 = self.graph.nodes[v]

                # Green and thick if this edge is on the shortest path
                key = (min(u, v), max(u, v))
                if key in path_edges:
                    color, width = EDGE_PATH, 4
                else:
                    color, width = EDGE_DEF, 2

                # Highlight edges from the first-selected edge node
                if self.edge_first in (u, v):
                    color, width = ACCENT, 2

                # Draw the edge line
                c.create_line(x1, y1, x2, y2, fill=color, width=width)

                # Draw weight label at edge midpoint inside a small oval
                mx, my = (x1+x2)/2, (y1+y2)/2
                c.create_oval(mx-14, my-11, mx+14, my+11,
                              fill=CANVAS_BG, outline=color)
                c.create_text(mx, my, text=str(w),
                              font=("Courier New", 8, "bold"), fill=color)

        # ── Draw nodes ─────────────────────────────────────────────
        for nid, (nx, ny) in self.graph.nodes.items():

            # Determine fill colour based on the node's algorithm state
            if nid == current:
                # Currently being processed — bright cyan
                fill, border, bw = ACCENT, TEXT_BRIGHT, 3
            elif nid in final_path:
                # On the final shortest path — green
                fill, border, bw = NODE_PATH, TEXT_BRIGHT, 3
            elif nid in visited:
                # Already finalised — gold
                fill, border, bw = NODE_VISIT, TEXT_BRIGHT, 2
            elif nid == self.start_node:
                # Source node — cyan
                fill, border, bw = NODE_START, TEXT_BRIGHT, 3
            elif nid == self.end_node:
                # Target node — orange
                fill, border, bw = NODE_END, TEXT_BRIGHT, 3
            elif nid == self.edge_first:
                # First node of an edge being added — highlighted cyan
                fill, border, bw = ACCENT, TEXT_BRIGHT, 2
            else:
                # Default unvisited node — dark blue
                fill, border, bw = NODE_DEF, NODE_BORDER, 2

            # Shadow (slightly offset dark oval for depth effect)
            c.create_oval(nx-NODE_R+3, ny-NODE_R+3,
                          nx+NODE_R+3, ny+NODE_R+3,
                          fill="#050710", outline="")

            # Node circle
            c.create_oval(nx-NODE_R, ny-NODE_R,
                          nx+NODE_R, ny+NODE_R,
                          fill=fill, outline=border, width=bw)

            # Node ID label inside the circle
            label_color = TEXT_BRIGHT if fill != NODE_DEF else TEXT_MAIN
            c.create_text(nx, ny, text=nid,
                          font=("Courier New", 11, "bold"), fill=label_color)

            # Distance label above the node (shown after algorithm runs)
            if dist and nid in dist:
                d_val = dist[nid]
                d_str = "∞" if d_val == float('inf') else str(d_val)
                c.create_text(nx, ny - NODE_R - 10, text=d_str,
                              font=("Courier New", 8), fill=ACCENT)

            # SRC / DST badge below the node
            if nid == self.start_node:
                c.create_text(nx, ny + NODE_R + 13, text="SRC",
                              font=("Courier New", 7, "bold"), fill=NODE_START)
            if nid == self.end_node:
                c.create_text(nx, ny + NODE_R + 13, text="DST",
                              font=("Courier New", 7, "bold"), fill=NODE_END)

    # ── Dijkstra's Algorithm execution & animation ────────────────────────────

    def _run_dijkstra(self):
        """Run Dijkstra's algorithm and animate the result on the canvas."""
        if not self._validate_for_run():
            return

        self.anim_running = True
        self._final_path  = []   # Clear any previous path highlight

        # Run the algorithm (returns immediately — animation done with after())
        dist, parent, visited_order, path = self.graph.dijkstra(
            self.start_node, self.end_node)

        self.anim_dist = dist
        self._update_dist_table(dist)   # Populate the distance table immediately

        # Begin step-by-step animation
        self._animate_dijkstra(visited_order, path, dist, 0, set())

    def _animate_dijkstra(self, visited_order, path, dist, step, visited_so_far):
        """
        Recursive animation function. Each call processes one node,
        redraws the canvas, then schedules itself again using after().
        This keeps the GUI responsive — no blocking sleep() calls needed.
        """
        if step < len(visited_order):
            node = visited_order[step]
            visited_so_far = visited_so_far | {node}   # Add this node to visited set

            # Redraw with the current node highlighted and distances shown
            self._redraw(visited=visited_so_far, current=node, dist=dist)
            self._update_status(
                f"Processing node '{node}'  |  dist[{node}] = {dist[node]}")

            # Schedule the next step after ANIM_DELAY milliseconds
            self.after(ANIM_DELAY,
                       lambda: self._animate_dijkstra(
                           visited_order, path, dist, step + 1, visited_so_far))
        else:
            # Animation complete — show final state with path highlighted
            self._final_path = path
            self._redraw(visited=visited_so_far, dist=dist)
            self.anim_running = False
            self._show_result(dist, path)

    def _step_through(self):
        """
        Initialise manual step-through mode.
        The 'Add Edge' button is repurposed as 'Next Step' so the user
        can advance the algorithm one node at a time by clicking it.
        """
        if not self._validate_for_run():
            return

        self._final_path = []
        dist, parent, visited_order, path = self.graph.dijkstra(
            self.start_node, self.end_node)

        # Store all step data in a dict so _next_step() can access it
        self._step_data = {
            "visited_order": visited_order,
            "path":          path,
            "dist":          dist,
            "step":          0,
            "visited_so_far": set(),
        }
        self._update_dist_table(dist)
        self._update_status(
            "Step-through ready. Click '▶▶ Next Step' to advance one step.")

        # Temporarily repurpose the Add Edge button as the Next Step button
        self.btn_add_edge.config(text="▶▶  Next Step",
                                  fg=ACCENT, command=self._next_step)

    def _next_step(self):
        """Advance the step-through animation by one node."""
        sd = self._step_data
        if sd["step"] < len(sd["visited_order"]):
            node = sd["visited_order"][sd["step"]]
            sd["visited_so_far"].add(node)
            self._redraw(visited=sd["visited_so_far"],
                         current=node, dist=sd["dist"])
            self._update_status(
                f"Step {sd['step']+1}: Finalising '{node}'  |  "
                f"dist = {sd['dist'][node]}")
            sd["step"] += 1
        else:
            # All nodes processed — show final result and restore button
            self._final_path = sd["path"]
            self._redraw(visited=sd["visited_so_far"], dist=sd["dist"])
            self._show_result(sd["dist"], sd["path"])
            self.btn_add_edge.config(text="⟷  Add Edge", fg=TEXT_MAIN,
                                      command=lambda: self._set_mode("add_edge"))

    def _validate_for_run(self):
        """
        Check all pre-conditions before running Dijkstra's.
        Returns True if all checks pass, False otherwise (with an error popup).
        """
        if len(self.graph.nodes) < 2:
            messagebox.showerror("Cannot Run",
                                 "Add at least 2 nodes to the graph first.")
            return False
        if not self.start_node or self.start_node not in self.graph.nodes:
            messagebox.showerror("Cannot Run",
                                 "Please set a valid source node first.\n"
                                 "(Use 'Set Source' button or right-click a node)")
            return False
        if not self.end_node or self.end_node not in self.graph.nodes:
            messagebox.showerror("Cannot Run",
                                 "Please set a valid target node first.\n"
                                 "(Use 'Set Target' button or right-click a node)")
            return False
        if self.start_node == self.end_node:
            messagebox.showerror("Cannot Run",
                                 "Source and target must be different nodes.")
            return False
        return True

    def _show_result(self, dist, path):
        """Display the shortest path result in the info panel and status bar."""
        d = dist.get(self.end_node, float('inf'))
        if not path or d == float('inf'):
            # No path found — graph may be disconnected
            self.lbl_dist.set("No path")
            self.lbl_path.set("—")
            self._update_status(
                f"✗ No path exists from '{self.start_node}' to '{self.end_node}'.")
        else:
            self.lbl_dist.set(str(d))
            self.lbl_path.set(" → ".join(path))
            self._update_status(
                f"✓ Shortest path: {' → '.join(path)}  |  Total distance: {d}")

    def _update_dist_table(self, dist):
        """Populate the distance table with shortest distances from source."""
        # Clear existing rows
        for row in self.dist_table.get_children():
            self.dist_table.delete(row)
        # Insert sorted rows (alphabetical by node ID)
        for node, d in sorted(dist.items()):
            label = "∞" if d == float('inf') else str(d)
            self.dist_table.insert("", "end", values=(node, label))

    # ── Utility actions ───────────────────────────────────────────────────────

    def _reset_view(self):
        """Clear the algorithm visualisation and return to the plain graph view."""
        self._final_path  = []
        self.anim_running = False
        self.lbl_dist.set("—")
        self.lbl_path.set("—")
        # Clear the distance table
        for row in self.dist_table.get_children():
            self.dist_table.delete(row)
        self._redraw()
        self._update_status("View reset. Modify graph or run algorithm again.")

    def _clear_all(self):
        """Delete all nodes and edges after confirmation."""
        if not messagebox.askyesno("Clear Graph",
                                   "Delete ALL nodes and edges?"):
            return
        self.graph.clear()
        self.node_counter = 0
        self.start_node   = None
        self.end_node     = None
        self._final_path  = []
        self.lbl_source.set("—")
        self.lbl_target.set("—")
        self.lbl_dist.set("—")
        self.lbl_path.set("—")
        for row in self.dist_table.get_children():
            self.dist_table.delete(row)
        self._update_graph_info()
        self._redraw()
        self._update_status("Graph cleared. Start adding nodes.")

    def _load_example(self):
        """
        Load a classic 7-node weighted graph for demonstration.

        Graph:  A-B(4), A-C(2), B-D(5), B-E(10),
                C-D(8), C-F(3), D-E(2), D-F(6),
                E-G(3), F-G(7)

        Shortest path A -> G = A → C → F → G (cost 12)
        """
        # Clear without asking for confirmation (internal load, not user action)
        self.graph.clear()
        self.node_counter = 0
        self.start_node   = None
        self.end_node     = None
        self._final_path  = []

        # Use canvas dimensions to centre the graph, with fallback defaults
        W = self.canvas.winfo_width()  or 900
        H = self.canvas.winfo_height() or 600
        cx, cy = W // 2, H // 2

        # Node positions arranged in a diamond/hex layout
        positions = {
            "A": (cx - 300, cy),
            "B": (cx - 150, cy - 160),
            "C": (cx - 150, cy + 160),
            "D": (cx,        cy),
            "E": (cx + 150,  cy - 160),
            "F": (cx + 150,  cy + 160),
            "G": (cx + 300,  cy),
        }
        for nid, (x, y) in positions.items():
            self.graph.add_node(nid, x, y)

        # Edge definitions: (node1, node2, weight)
        edges = [
            ("A","B",4), ("A","C",2), ("B","D",5), ("B","E",10),
            ("C","D",8), ("C","F",3), ("D","E",2), ("D","F",6),
            ("E","G",3), ("F","G",7),
        ]
        for u, v, w in edges:
            self.graph.add_edge(u, v, w)

        # Set A as source, G as target
        self.node_counter = 7
        self.start_node   = "A"
        self.end_node     = "G"
        self.lbl_source.set("A")
        self.lbl_target.set("G")

        self._update_graph_info()
        self._redraw()
        self._update_status(
            "Example loaded (7 nodes, 10 edges). Click '▶ Run Dijkstra's' to visualise.")

    def _save_graph(self):
        """Serialise the current graph and session state to saved_graph.json."""
        save_path = os.path.join(
            os.path.dirname(os.path.abspath(__file__)), "saved_graph.json")
        data = self.graph.to_dict()
        data["start"]   = self.start_node
        data["end"]     = self.end_node
        data["counter"] = self.node_counter
        with open(save_path, "w") as f:
            json.dump(data, f, indent=2)
        self._update_status(f"Graph saved → saved_graph.json")

    def _load_graph_file(self):
        """Load a previously saved graph from saved_graph.json."""
        load_path = os.path.join(
            os.path.dirname(os.path.abspath(__file__)), "saved_graph.json")
        if not os.path.exists(load_path):
            messagebox.showinfo("Load Graph", "No saved graph found.")
            return
        with open(load_path, "r") as f:
            data = json.load(f)
        self.graph.from_dict(data)
        self.start_node   = data.get("start")
        self.end_node     = data.get("end")
        self.node_counter = data.get("counter", len(self.graph.nodes))
        self._final_path  = []
        self.lbl_source.set(self.start_node or "—")
        self.lbl_target.set(self.end_node   or "—")
        self._update_graph_info()
        self._redraw()
        self._update_status("Graph loaded from saved_graph.json")

    def _exit(self):
        """Ask for confirmation before closing the application."""
        if messagebox.askyesno("Exit",
                               "Are you sure you want to exit\nShortest Path Finder?"):
            self.destroy()


# ==============================================================================
#  ENTRY POINT
# ==============================================================================
if __name__ == "__main__":
    app = App()
    app.mainloop()
