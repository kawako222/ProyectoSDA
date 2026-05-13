"""
Simulador de Grafos — Parcial 3 (Edición BT21 Aesthetic)
Etapa 1: BFS, DFS, Profundidad Limitada, Profundidad Iterativa
Etapa 2: A* con pesos de terreno (Manhattan y Euclidiana)
Etapa 3: Kruskal y Prim (MST sobre nodos dispersos)
"""

import pygame
import math
import sys
from collections import deque
import heapq

# ══════════════════════════════════════════════════════════════════════════════
# CONSTANTES DE PANTALLA
# ══════════════════════════════════════════════════════════════════════════════
ANCHO_MAPA  = 600
ANCHO_PANEL = 280
ALTO        = 660
VENTANA_W   = ANCHO_MAPA + ANCHO_PANEL
FILAS       = 30
ANCHO_CELDA = ANCHO_MAPA // FILAS

# ══════════════════════════════════════════════════════════════════════════════
# PALETA AESTHETIC BT21 (Tonos Pastel)
# ══════════════════════════════════════════════════════════════════════════════
BG_APP   = (250, 242, 255)  # Lila muy claro (Fondo principal)
BG_PANEL = (245, 235, 250)  # Rosa lila suave (Panel lateral)
BG_CARD  = (255, 255, 255)  # Blanco puro (Botones no activos)
ACCENT   = (255, 140, 180)  # Rosa pastel vibrante
ACCENT2  = (140, 200, 255)  # Azul cielo pastel
ACCENT3  = (150, 230, 180)  # Verde menta pastel
TEXT_MN  = (90,  75,  100)  # Morado oscuro (Texto principal)
TEXT_DIM = (160, 145, 170)  # Morado grisáceo (Texto secundario)
LINE_C   = (235, 220, 245)  # Líneas separadoras lila claro

C_LIBRE  = (255, 250, 255)  # Casi blanco para celdas libres
C_MURO   = (100,  90, 110)  # Color base de muro (si no hay imagen)
C_LODO   = (200, 160, 140)  # Color base de lodo (si no hay imagen)
C_INICIO = (140, 230, 160)  # Verde pastel
C_FIN    = (255, 120, 120)  # Rojo/Rosa pastel
C_CAMINO = (255,  20, 147)  # Rosa Brillante (Hot Pink) para el camino final
C_GRID   = (235, 225, 245)  # Cuadrícula lila muy sutil

# Colores de exploración (Tonos pastel)
C_BFS  = (180, 220, 255)   # Azul bebé
C_DFS  = (220, 180, 255)   # Lila pastel
C_DLS  = (255, 200, 150)   # Durazno pastel
C_IDA  = (160, 240, 220)   # Menta claro
C_ASTR = (255, 180, 220)   # Rosa pastel

# MST
C_NODO_MST = (255, 180, 220)
C_ARI_PRIM = (140, 200, 255)
C_ARI_KRUS = (255, 160, 180)
C_ARI_GRAY = (200, 190, 210)

# Variables globales para las imágenes
IMG_TATA = None
IMG_COOKY = None
IMG_SHOOKY = None
IMG_RJ = None

# ══════════════════════════════════════════════════════════════════════════════
# UNION-FIND (Lógica Intocable)
# ══════════════════════════════════════════════════════════════════════════════
class UnionFind:
    def __init__(self, n):
        self.parent = list(range(n))
        self.rank   = [0] * n

    def find(self, i):
        if self.parent[i] != i:
            self.parent[i] = self.find(self.parent[i])
        return self.parent[i]

    def union(self, i, j):
        ri, rj = self.find(i), self.find(j)
        if ri == rj: return False
        if   self.rank[ri] < self.rank[rj]: self.parent[ri] = rj
        elif self.rank[ri] > self.rank[rj]: self.parent[rj] = ri
        else: self.parent[rj] = ri; self.rank[ri] += 1
        return True

# ══════════════════════════════════════════════════════════════════════════════
# NODO CUADRÍCULA (Modificado para soportar imágenes sin alterar lógica)
# ══════════════════════════════════════════════════════════════════════════════
class Nodo:
    def __init__(self, fila, col):
        self.fila  = fila
        self.col   = col
        self.color = C_LIBRE
        self.costo = 1

    def es_muro(self):     return self.costo == float('inf')
    def es_inicio(self):   return self.color == C_INICIO
    def es_fin(self):      return self.color == C_FIN
    def es_especial(self): return self.es_inicio() or self.es_fin()

    def hacer_muro(self):  self.color = C_MURO;  self.costo = float('inf')
    def hacer_lodo(self):  self.color = C_LODO;  self.costo = 5
    def hacer_libre(self): self.color = C_LIBRE; self.costo = 1
    def hacer_inicio(self):self.color = C_INICIO;self.costo = 1
    def hacer_fin(self):   self.color = C_FIN;   self.costo = 1

    def hacer_explorado(self, c):
        if not self.es_especial(): self.color = c
    def hacer_camino(self):
        if not self.es_especial(): self.color = C_CAMINO

    def dibujar(self, v):
        x = self.fila * ANCHO_CELDA
        y = self.col * ANCHO_CELDA
        
        # 1. Dibujar el color de fondo (necesario para el camino o color base)
        pygame.draw.rect(v, self.color, (x, y, ANCHO_CELDA, ANCHO_CELDA))
        
        # 2. Renderizar imágenes de BT21 por encima si aplican y están cargadas
        if self.es_inicio() and IMG_TATA:
            v.blit(IMG_TATA, (x, y))
        elif self.es_fin() and IMG_COOKY:
            v.blit(IMG_COOKY, (x, y))
        elif self.es_muro() and IMG_SHOOKY:
            v.blit(IMG_SHOOKY, (x, y))
        elif self.costo == 5 and IMG_RJ:
            v.blit(IMG_RJ, (x, y))

# ══════════════════════════════════════════════════════════════════════════════
# UTILIDADES DE CUADRÍCULA (Lógica Intocable)
# ══════════════════════════════════════════════════════════════════════════════
def crear_cuadricula():
    return [[Nodo(f, c) for c in range(FILAS)] for f in range(FILAS)]

EXP_COLORS = {C_BFS, C_DFS, C_DLS, C_IDA, C_ASTR, C_CAMINO}

def limpiar_busqueda(grid, ini, fin):
    for fila in grid:
        for n in fila:
            if n.es_especial(): continue
            if n.color in EXP_COLORS:
                if   n.costo == float('inf'): n.color = C_MURO
                elif n.costo == 5:            n.color = C_LODO
                else:                         n.color = C_LIBRE

def reiniciar_todo(grid, ini, fin):
    for fila in grid:
        for n in fila: n.hacer_libre()
    ini.hacer_inicio(); fin.hacer_fin()

def vecinos(n, grid):
    res = []
    for df, dc in [(-1,0),(1,0),(0,-1),(0,1)]:
        nf, nc = n.fila+df, n.col+dc
        if 0 <= nf < FILAS and 0 <= nc < FILAS:
            v = grid[nf][nc]
            if not v.es_muro(): res.append(v)
    return res

def reconstruir(came, fin):
    n = fin; cost = 0
    while n in came:
        n = came[n]; n.hacer_camino(); cost += n.costo
    return cost

def pos_a_nodo(pos, grid):
    mx, my = pos
    if not (0 <= mx < ANCHO_MAPA and 0 <= my < ALTO): return None
    f, c = mx//ANCHO_CELDA, my//ANCHO_CELDA
    if 0 <= f < FILAS and 0 <= c < FILAS: return grid[f][c]
    return None

# ══════════════════════════════════════════════════════════════════════════════
# ESTADÍSTICAS
# ══════════════════════════════════════════════════════════════════════════════
stats = {"algo":"—","visitados":0,"costo":0,"estado":"Listo",
         "limite_d":5,"comparativa":[]}

# ══════════════════════════════════════════════════════════════════════════════
# ALGORITMOS — ETAPAS 1, 2 Y 3 (Lógica Intocable)
# ══════════════════════════════════════════════════════════════════════════════
def _chk():
    for ev in pygame.event.get():
        if ev.type == pygame.QUIT: pygame.quit(); sys.exit()

def bfs(grid, ini, fin, draw):
    stats.update({"algo":"BFS","visitados":0,"costo":0,"estado":"Buscando…"})
    cola = deque([ini]); vis = {ini}; came = {}
    while cola:
        _chk(); actual = cola.popleft()
        if actual == fin:
            stats["costo"] = reconstruir(came, fin); stats["estado"]="¡Encontrado!"
            draw(); return True
        for v in vecinos(actual, grid):
            if v not in vis:
                vis.add(v); came[v]=actual; cola.append(v)
                v.hacer_explorado(C_BFS); stats["visitados"]+=1
        draw(); pygame.time.delay(5)
    stats["estado"]="Sin camino"; return False

def dfs(grid, ini, fin, draw):
    stats.update({"algo":"DFS","visitados":0,"costo":0,"estado":"Buscando…"})
    pila = [ini]; vis = {ini}; came = {}
    while pila:
        _chk(); actual = pila.pop()
        if actual == fin:
            stats["costo"] = reconstruir(came, fin); stats["estado"]="¡Encontrado!"
            draw(); return True
        for v in vecinos(actual, grid):
            if v not in vis:
                vis.add(v); came[v]=actual; pila.append(v)
                v.hacer_explorado(C_DFS); stats["visitados"]+=1
        draw(); pygame.time.delay(5)
    stats["estado"]="Sin camino"; return False

def dls(grid, ini, fin, limite, draw):
    stats.update({"algo":f"DLS L={limite}","visitados":0,"costo":0,"estado":"Buscando…"})
    came = {}
    def _rec(nd, prof, vis):
        if nd == fin: return True
        if prof == 0: return False
        for v in vecinos(nd, grid):
            if v not in vis:
                vis.add(v); came[v]=nd
                v.hacer_explorado(C_DLS); stats["visitados"]+=1
                _chk(); draw(); pygame.time.delay(5)
                if _rec(v, prof-1, vis): return True
        return False
    ok = _rec(ini, limite, {ini})
    if ok:
        stats["costo"]=reconstruir(came,fin); stats["estado"]="¡Encontrado!"
    else:
        stats["estado"]="Sin camino (límite)"
    draw(); return ok

def iddfs(grid, ini, fin, draw):
    stats.update({"algo":"IDDFS","visitados":0,"costo":0,"estado":"Buscando…"})
    for lim in range(1, FILAS*FILAS):
        came={}; vis={ini}; stats["algo"]=f"IDDFS L={lim}"
        def _rec(nd, prof):
            if nd==fin: return True
            if prof==0: return False
            for v in vecinos(nd, grid):
                if v not in vis:
                    vis.add(v); came[v]=nd
                    v.hacer_explorado(C_IDA); stats["visitados"]+=1
                    _chk(); draw(); pygame.time.delay(3)
                    if _rec(v,prof-1): return True
            return False
        if _rec(ini, lim):
            stats["costo"]=reconstruir(came,fin); stats["estado"]=f"¡Listo L={lim}!"
            draw(); return True
        limpiar_busqueda(grid, ini, fin); ini.hacer_inicio(); fin.hacer_fin()
    stats["estado"]="Sin camino"; return False

def h(a, b, modo):
    if modo=="manhattan": return abs(a.fila-b.fila)+abs(a.col-b.col)
    return math.hypot(a.fila-b.fila, a.col-b.col)

def a_star(grid, ini, fin, draw, modo="manhattan"):
    stats.update({"algo":f"A*-{modo}","visitados":0,"costo":0,"estado":"Buscando…"})
    cnt=0; heap=[]; heapq.heappush(heap,(0,cnt,ini))
    came={}; g={n:float("inf") for row in grid for n in row}
    g[ini]=0; open_h={ini}
    while heap:
        _chk(); _,_,actual = heapq.heappop(heap); open_h.discard(actual)
        if actual==fin:
            reconstruir(came,fin)
            stats["costo"]=round(g[fin],1); stats["estado"]="¡Encontrado!"
            draw(); return True
        for v in vecinos(actual, grid):
            ng = g[actual]+v.costo
            if ng < g[v]:
                came[v]=actual; g[v]=ng; fv=ng+h(v,fin,modo)
                if v not in open_h:
                    cnt+=1; heapq.heappush(heap,(fv,cnt,v))
                    open_h.add(v); v.hacer_explorado(C_ASTR); stats["visitados"]+=1
        draw(); pygame.time.delay(5)
    stats["estado"]="Sin camino"; return False

class NodoMST:
    def __init__(self, px, py, idx):
        self.px=px; self.py=py; self.idx=idx

    def dibujar(self, surf, fuente):
        pygame.draw.circle(surf, C_NODO_MST, (self.px,self.py), 11)
        pygame.draw.circle(surf, TEXT_MN,    (self.px,self.py), 11, 2)
        t = fuente.render(str(self.idx), True, TEXT_MN)
        surf.blit(t, (self.px-t.get_width()//2, self.py-t.get_height()//2))

def dist_mst(a, b): return math.hypot(a.px-b.px, a.py-b.py)

def prim_mst(nodos, draw):
    n=len(nodos); vis={0}; aris=[]; heap=[]
    for j in range(1,n):
        heapq.heappush(heap,(dist_mst(nodos[0],nodos[j]),0,j))
    while heap and len(vis)<n:
        _chk(); p,i,j = heapq.heappop(heap)
        if j in vis: continue
        vis.add(j); aris.append((i,j,p))
        for k in range(n):
            if k not in vis:
                heapq.heappush(heap,(dist_mst(nodos[j],nodos[k]),j,k))
        draw(aris,"Prim"); pygame.time.delay(500)
    return aris

def kruskal_mst(nodos, draw):
    n=len(nodos)
    todas=[(dist_mst(nodos[i],nodos[j]),i,j)
           for i in range(n) for j in range(i+1,n)]
    todas.sort(); uf=UnionFind(n); mst=[]
    for p,i,j in todas:
        _chk()
        if uf.union(i,j):
            mst.append((i,j,p)); draw(mst,"Kruskal"); pygame.time.delay(500)
    return mst

# ══════════════════════════════════════════════════════════════════════════════
# PANEL LATERAL
# ══════════════════════════════════════════════════════════════════════════════
def dibujar_panel(ventana, fb, fn, fs, etapa, limite_d):
    px = ANCHO_MAPA
    pygame.draw.rect(ventana, BG_PANEL, (px, 0, ANCHO_PANEL, ALTO))

    def blit(texto, y, color=TEXT_MN, f=None, ox=10):
        s = (f or fn).render(texto, True, color)
        ventana.blit(s, (px+ox, y))

    def linea(y):
        pygame.draw.line(ventana, LINE_C, (px+8,y), (px+ANCHO_PANEL-8,y))

    # ── Título
    blit("SIMULADOR BT21 AESTHETIC", 10, ACCENT, fb)
    linea(30)

    # ── Etapa
    nombres = {1:"Etapa 1 · Exploración ciega",
               2:"Etapa 2 · A* Inteligente",
               3:"Etapa 3 · MST"}
    blit(nombres[etapa], 36, ACCENT2, fs)
    linea(52)

    # ── Stats
    blit(f"Algoritmo : {stats['algo']}",      58, TEXT_MN, fs)
    blit(f"Visitados : {stats['visitados']}",  72, ACCENT3,  fs)
    blit(f"Costo     : {stats['costo']}",      86, ACCENT,   fs)
    ce = ACCENT3 if "Encontrado" in stats["estado"] or "Listo" in stats["estado"] \
         else (255,90,90) if "Sin" in stats["estado"] else TEXT_DIM
    blit(f"Estado    : {stats['estado']}", 100, ce, fs)
    linea(118)

    # ── Comparativa
    blit("Comparativa:", 124, TEXT_DIM, fs)
    comp = stats["comparativa"][-5:]
    for i,(nm,vi,co) in enumerate(comp):
        blit(f"  {nm[:10]:<10}  V:{vi:<5} C:{co}", 138+i*14, TEXT_MN, fs)
    linea(212)

    # ── Controles generales
    blit("CONTROLES GENERALES", 218, ACCENT, fb)
    controles_gral = [
        ("Clic Izq",  "Shooky / Muro"),
        ("Clic Der",  "RJ / Lodo (Cost 5)"),
        ("Clic Med",  "Borrar celda"),
        ("R",         "Reiniciar todo"),
        ("1 / 2 / 3", "Cambiar etapa"),
    ]
    for i,(k,d) in enumerate(controles_gral):
        y = 234 + i*14
        blit(f"  {k:<10}", y, ACCENT,   fs)
        blit(f"              {d}", y, TEXT_MN, fs)
    linea(308)

    # ── Controles por etapa
    if etapa == 1:
        blit("ETAPA 1 — EXPLORACIÓN", 314, ACCENT2, fb)
        et1 = [
            ("B", "BFS          ",  C_BFS ),
            ("D", "DFS          ",  C_DFS ),
            (f"L", f"DLS  (L={limite_d})   ", C_DLS ),
            ("I", "IDDFS        ",  C_IDA ),
            ("+/-","Ajustar L    ", TEXT_DIM),
            ("C",  "Limpiar vis. ", TEXT_DIM),
        ]
        for i,(k,d,c) in enumerate(et1):
            y=330+i*16
            blit(f"  {k:<4}", y, ACCENT, fs)
            blit(f"      {d}", y, c if c != TEXT_DIM else TEXT_MN, fs)

    elif etapa == 2:
        blit("ETAPA 2 — A*", 314, ACCENT2, fb)
        et2 = [
            ("A","A* Manhattan  ", C_ASTR),
            ("E","A* Euclidiana ", C_ASTR),
            ("B","BFS (comparar)",C_BFS ),
            ("C","Limpiar vis.  ",TEXT_DIM),
        ]
        for i,(k,d,c) in enumerate(et2):
            y=330+i*16
            blit(f"  {k:<4}", y, ACCENT, fs)
            blit(f"      {d}", y, c if c != TEXT_DIM else TEXT_MN, fs)

    else:
        blit("ETAPA 3 — MST", 314, ACCENT2, fb)
        et3 = [
            ("Clic", "Añadir nodo MST", TEXT_MN),
            ("P",    "Prim           ", C_ARI_PRIM),
            ("K",    "Kruskal        ", C_ARI_KRUS),
            ("X",    "Borrar nodos   ", TEXT_DIM),
        ]
        for i,(k,d,c) in enumerate(et3):
            y=330+i*16
            blit(f"  {k:<5}", y, ACCENT, fs)
            blit(f"       {d}", y, c if c != TEXT_DIM else TEXT_MN, fs)

    linea(ALTO-90)

    # ── Botones de etapa
    blit("CAMBIAR ETAPA", ALTO-84, ACCENT, fb)
    tab_labels = [("1 · Ciega",C_BFS),("2 · A*",C_ASTR),("3 · MST",C_ARI_PRIM)]
    bw = (ANCHO_PANEL-20)//3
    for i,(lbl,col) in enumerate(tab_labels):
        bx = px+10+i*bw; by = ALTO-64
        activo = (i+1)==etapa
        pygame.draw.rect(ventana, BG_CARD if not activo else (235, 215, 245),
                         (bx,by,bw-4,26), border_radius=5)
        if activo:
            pygame.draw.rect(ventana, col, (bx,by,bw-4,26), 2, border_radius=5)
        s = fs.render(lbl, True, col if activo else TEXT_DIM)
        ventana.blit(s, (bx+(bw-4-s.get_width())//2, by+5))

    linea(ALTO-34)

    # ── Leyenda
    ley = [(C_INICIO,"Tata"),(C_FIN,"Cooky"),(C_MURO,"Shk"),(C_LODO,"RJ"),(C_CAMINO,"Ruta")]
    lw = (ANCHO_PANEL-16)//len(ley)
    for i,(col,nom) in enumerate(ley):
        lx=px+8+i*lw
        pygame.draw.rect(ventana, col, (lx, ALTO-24, 12, 12))
        ventana.blit(fs.render(nom, True, TEXT_DIM), (lx+14, ALTO-26))

# ══════════════════════════════════════════════════════════════════════════════
# DIBUJO CUADRÍCULA
# ══════════════════════════════════════════════════════════════════════════════
def dibujar_grid(ventana, grid):
    for fila in grid:
        for n in fila: n.dibujar(ventana)
    for i in range(FILAS+1):
        pygame.draw.line(ventana, C_GRID, (i*ANCHO_CELDA,0),(i*ANCHO_CELDA,FILAS*ANCHO_CELDA))
        pygame.draw.line(ventana, C_GRID, (0,i*ANCHO_CELDA),(FILAS*ANCHO_CELDA,i*ANCHO_CELDA))

# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════
def main():
    pygame.init()
    ventana = pygame.display.set_mode((VENTANA_W, ALTO))
    pygame.display.set_caption("Simulador BT21 — Búsqueda de Grafos")

    global IMG_TATA, IMG_COOKY, IMG_SHOOKY, IMG_RJ

    # ══════════════════════════════════════════════════════════════════════════
    # CARGA DE IMÁGENES BT21 (Usa try/except para no crashear si faltan)
    # ══════════════════════════════════════════════════════════════════════════
    try:
        # [AQUÍ IMAGEN]: Carga tu archivo para TATA (Inicio)
        IMG_TATA = pygame.image.load("./bt21/bt21.png").convert_alpha()
        IMG_TATA = pygame.transform.scale(IMG_TATA, (ANCHO_CELDA, ANCHO_CELDA))
    except: pass

    try:
        # [AQUÍ IMAGEN]: Carga tu archivo para COOKY (Fin)
        IMG_COOKY = pygame.image.load("./bt21/chimi.png").convert_alpha()
        IMG_COOKY = pygame.transform.scale(IMG_COOKY, (ANCHO_CELDA, ANCHO_CELDA))
    except: pass

    try:
        # [AQUÍ IMAGEN]: Carga tu archivo para SHOOKY (Muros/Negro)
        IMG_SHOOKY = pygame.image.load("./bt21/jk.png").convert_alpha()
        IMG_SHOOKY = pygame.transform.scale(IMG_SHOOKY, (ANCHO_CELDA, ANCHO_CELDA))
    except: pass

    try:
        # [AQUÍ IMAGEN]: Carga tu archivo para RJ o MANG (Lodo/Café)
        IMG_RJ = pygame.image.load("./bt21/rj.png").convert_alpha()
        IMG_RJ = pygame.transform.scale(IMG_RJ, (ANCHO_CELDA, ANCHO_CELDA))
    except: pass
    # ══════════════════════════════════════════════════════════════════════════

    fb = pygame.font.SysFont("Consolas", 13, bold=True)
    fn = pygame.font.SysFont("Consolas", 12)
    fs = pygame.font.SysFont("Consolas", 11)

    grid  = crear_cuadricula()
    ini   = grid[2][2];  ini.hacer_inicio()
    fin   = grid[27][27]; fin.hacer_fin()

    etapa       = 1
    ejecutando  = False
    nodos_mst   = []
    aristas_mst = []
    algo_mst    = "—"

    def dibujar(aris=None, nom_mst="—"):
        ventana.fill(BG_APP)
        if etapa in (1, 2):
            dibujar_grid(ventana, grid)
        else:
            pygame.draw.rect(ventana, (250,242,255), (0,0,ANCHO_MAPA,ALTO))
            for i in range(len(nodos_mst)):
                for j in range(i+1, len(nodos_mst)):
                    a,b = nodos_mst[i], nodos_mst[j]
                    pygame.draw.line(ventana, C_ARI_GRAY, (a.px,a.py),(b.px,b.py),1)
                    mx=(a.px+b.px)//2; my=(a.py+b.py)//2
                    d=round(dist_mst(a,b),0)
                    ventana.blit(fs.render(str(int(d)),True,TEXT_DIM),(mx,my))
            if aris:
                col_ar = C_ARI_PRIM if nom_mst=="Prim" else C_ARI_KRUS
                for i,j,_ in aris:
                    a,b=nodos_mst[i],nodos_mst[j]
                    pygame.draw.line(ventana, col_ar,(a.px,a.py),(b.px,b.py),4)
            for nm in nodos_mst:
                nm.dibujar(ventana, fs)
        dibujar_panel(ventana, fb, fn, fs, etapa, stats["limite_d"])
        pygame.display.update()

    def draw_simple():
        dibujar(aristas_mst, algo_mst)

    def run(fn, *args):
        nonlocal ejecutando
        ejecutando = True
        limpiar_busqueda(grid, ini, fin)
        ini.hacer_inicio(); fin.hacer_fin()
        if args:
            fn(*args, draw_simple)
        else:
            fn(draw_simple)
        stats["comparativa"].append((stats["algo"], stats["visitados"], stats["costo"]))
        ejecutando = False

    clock = pygame.time.Clock()
    corriendo = True

    while corriendo:
        dibujar(aristas_mst, algo_mst)

        for evento in pygame.event.get():
            if evento.type == pygame.QUIT:
                corriendo = False

            if evento.type == pygame.KEYDOWN:
                if evento.key == pygame.K_1: etapa = 1
                if evento.key == pygame.K_2: etapa = 2
                if evento.key == pygame.K_3: etapa = 3

            if ejecutando: continue

            mb  = pygame.mouse.get_pressed()
            pos = pygame.mouse.get_pos()

            if etapa in (1, 2):
                nd = pos_a_nodo(pos, grid)
                if nd and not nd.es_especial():
                    if mb[0]: nd.hacer_muro()
                    elif mb[2]: nd.hacer_lodo()
                    elif mb[1]: nd.hacer_libre()
            else:
                if evento.type == pygame.MOUSEBUTTONDOWN and evento.button == 1:
                    if pos[0] < ANCHO_MAPA:
                        nodos_mst.append(NodoMST(pos[0], pos[1], len(nodos_mst)))
                        aristas_mst = []

            if evento.type == pygame.KEYDOWN:
                k = evento.key

                if etapa == 1:
                    if k == pygame.K_b: run(bfs,  grid, ini, fin)
                    if k == pygame.K_d: run(dfs,  grid, ini, fin)
                    if k == pygame.K_l: run(dls,  grid, ini, fin, stats["limite_d"])
                    if k == pygame.K_i: run(iddfs, grid, ini, fin)
                    if k in (pygame.K_PLUS, pygame.K_KP_PLUS, pygame.K_EQUALS):
                        stats["limite_d"] = min(stats["limite_d"]+1, 60)
                    if k in (pygame.K_MINUS, pygame.K_KP_MINUS):
                        stats["limite_d"] = max(1, stats["limite_d"]-1)
                    if k == pygame.K_c:
                        limpiar_busqueda(grid, ini, fin)
                        ini.hacer_inicio(); fin.hacer_fin()

                elif etapa == 2:
                    if k == pygame.K_a: run(lambda d: a_star(grid, ini, fin, d, "manhattan"))
                    if k == pygame.K_e: run(lambda d: a_star(grid, ini, fin, d, "euclidiana"))
                    if k == pygame.K_b: run(bfs,   grid, ini, fin)
                    if k == pygame.K_c:
                        limpiar_busqueda(grid, ini, fin)
                        ini.hacer_inicio(); fin.hacer_fin()

                elif etapa == 3:
                    if k == pygame.K_p and len(nodos_mst) >= 2:
                        ejecutando = True; algo_mst = "Prim"
                        def dib_p(ars, nom):
                            nonlocal aristas_mst, algo_mst
                            aristas_mst=ars; algo_mst=nom; dibujar(aris=ars,nom_mst=nom)
                        aristas_mst = prim_mst(nodos_mst, dib_p)
                        ct = round(sum(p for _,_,p in aristas_mst),1)
                        stats.update({"algo":"Prim","visitados":len(aristas_mst),
                                      "costo":ct,"estado":"MST listo"})
                        ejecutando = False

                    if k == pygame.K_k and len(nodos_mst) >= 2:
                        ejecutando = True; algo_mst = "Kruskal"
                        def dib_k(ars, nom):
                            nonlocal aristas_mst, algo_mst
                            aristas_mst=ars; algo_mst=nom; dibujar(aris=ars,nom_mst=nom)
                        aristas_mst = kruskal_mst(nodos_mst, dib_k)
                        ct = round(sum(p for _,_,p in aristas_mst),1)
                        stats.update({"algo":"Kruskal","visitados":len(aristas_mst),
                                      "costo":ct,"estado":"MST listo"})
                        ejecutando = False

                    if k == pygame.K_x:
                        nodos_mst.clear(); aristas_mst=[]
                        stats.update({"algo":"—","visitados":0,"costo":0,"estado":"Listo"})

                if k == pygame.K_r:
                    reiniciar_todo(grid, ini, fin)
                    nodos_mst.clear(); aristas_mst=[]
                    stats.update({"algo":"—","visitados":0,"costo":0,
                                  "estado":"Listo","comparativa":[]})

        clock.tick(60)
    pygame.quit()

if __name__ == "__main__":
    main()