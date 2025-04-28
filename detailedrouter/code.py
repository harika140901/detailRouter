import LEFDEFParser
from LEFDEFParser import Rect
import re
from collections import defaultdict
import heapq as hq
import math
import checker
blockers = {}
blockers['li1'] = []
blockers['met1'] = []
blockers['met2'] = []
blockers['met3'] = []
blockers['met4'] = []
blockers['met5'] = []

########################################guide file parser########################
class Rectangleguide:
    def __init__(self, x1, y1, x2, y2, layer):
        self.x1 = int(x1)
        self.y1 = int(y1)
        self.x2 = int(x2)
        self.y2 = int(y2)
        self.layer = layer
    def __repr__(self):
        return f"({self.x1}, {self.y1}, {self.x2}, {self.y2}) on {self.layer}"
    def area(self):
        return abs(self.x2 - self.x1) * abs(self.y2 - self.y1)
    def overlaps(self, other):
        return not (self.x2 <= other.x1 or self.x1 >= other.x2 or
                    self.y2 <= other.y1 or self.y1 >= other.y2)
    def inside(self,v):
        if self.x2 > v._xy[0] and self.x1 < v._xy[0] and self.y2 > v._xy[1] and self.y1 < v._xy[1]:
            return True
        else:
            return False

class Netguide:
    def __init__(self, name):
        self.name = name
        self.shapes = []
    def add_shape(self, rect):
        self.shapes.append(rect)
    def get_shapes_by_layer(self, layer):
        return [r for r in self.shapes if r.layer == layer]
    def __repr__(self):
        return f"Net {self.name} with {len(self.shapes)} shapes"

def parse_shape_file(filename):
    with open(filename, 'r') as f:
        lines = f.readlines()

    nets = {}
    current_net = None
    in_block = False

    for line in lines:
        line = line.strip()
        if not line:
            continue

        if re.match(r'^[\w\[\]_]+$', line):
            current_net = line
            if current_net not in nets:
                nets[current_net] = Netguide(current_net)

        elif line == '(':
            in_block = True

        elif line == ')':
            in_block = False

        elif in_block and current_net:
            tokens = line.split()
            if len(tokens) == 5:
                x1, y1, x2, y2, layer = tokens
                rect = Rectangleguide(x1, y1, x2, y2, layer)
                nets[current_net].add_shape(rect)

    return nets
########################################################################
#astar
class PriorityQueue:
    def __init__(self, vertices=[]):
        self._q = vertices[:]
        hq.heapify(self._q)

    def push(self, v):
        hq.heappush(self._q, v)

    def pop(self):
        return hq.heappop(self._q)

    def update(self, v, cost):
        # Update vertex in priority queue
        try:
            i = self._q.index(v)
        except ValueError:
            return
        if i is not None:
            v._cost = cost
            v._f = v._cost + v._h  # recalculate f = g + h for A*
            hq.heapify(self._q)

    def empty(self):
        return len(self._q) == 0

    def __contains__(self, v):
        return v in self._q

    def __repr__(self):
        return str(self._q)

def dist(u, v):
    return abs(u._xy[0] - v._xy[0]) + abs(u._xy[1] - v._xy[1])

def blocked(v,layer):
    if layer not in blockers.keys():
        return False
    b = False
    for rects in blockers[layer]:
        if rects.ur.x > v._xy[0] and rects.ll.x < v._xy[0] and rects.ur.y > v._xy[1] and rects.ll.y < v._xy[1]:
            b = True
            break
    return b

def notInsideGuide(v,layer):
    b = True
    for rects in blockers[layer]:
        if rects.ur.x > v._xy[0] and rects.ll.x < v._xy[0] and rects.ur.y > v._xy[1] and rects.ll.y < v._xy[1]:
            b = False
            break
    return b

def astar(V, s, t):
    for v in V:
        v._h = dist(v, t)

    s._cost = 0
    Q = PriorityQueue(V)
    alreadyEvaluated = []

    while not Q.empty():
        u = Q.pop()
        if u == t:
            break
        alreadyEvaluated.append(u)
        for layer, neighbors in u._nbrs.items():
            for v in neighbors:
                if blocked(v, layer):
                    continue
                if notInsideGuide(v, layer):
                    continue
                if v in alreadyEvaluated:
                    continue
                gnew = u._cost + dist(u, v)+ (10 if layer != v._layer[0] else 0)
                if v not in Q:
                    Q.push(v)
                if gnew < v._cost:
                    Q.update(v, gnew)
                    v._parent = u

    path = []
    while t._parent is not None:
        path.append(t)
        t = t._parent
    # path.append(s)
    path.reverse()
    return path

###############################################################
class Comp:
    def __init__(self, comp, dim):
        self._comp = comp      
        self._dim = dim        
        self._nbrs = []        
        self._index = -1      

    def __repr__(self):
        return f'{self._comp.name()}'
    

class Vertex:
    def __init__(self, x, y, cost=math.inf, h=0, parent=None, layer=[]):
        self._xy = (x, y)
        self._cost = cost
        self._parent = parent
        self._layer = layer
        self._nbrs = {}
        self._h = h 
        self._f = self._cost + self._h 

    def __lt__(self, other):
        return self._f < other._f 

    def __eq__(self, other):
        return self._xy == other._xy

    def __repr__(self):
        return f'(xy:{self._xy}, cost:{self._cost}, f:{self._f})'
    
    def appendLayer(self, layertoAdd):
        self._layer.append(layertoAdd)


# def addboundaryPINS(listOfVertices): #to metal tracks grid list
#     Vertex(x,y,[])

def bloatguideLines(bloatWithX, bloatWithY, netguide):
    for rect in netguide.shapes:
        rect.x1 = rect.x1 - bloatWithX
        rect.x2 = rect.x2 + bloatWithX
        rect.y1 = rect.y1 - bloatWithY
        rect.y2 = rect.y2 + bloatWithY
    return netguide

def gridInsideGuide(metaltracks, netguide):
    xcord = []
    ycord = []
    listOfVertices = []
    grid_map = {}  # (x, y) -> Vertex

    # Step 1: Collect valid x and y coordinates from metal tracks
    for layer in set(rect.layer for rect in netguide.shapes):  # layer just to pass one layer at a time
        if layer == 'li1':
            continue
        if metaltracks[layer][1] == 1:
            for i in range(metaltracks[layer][0][1].num):
                y = metaltracks[layer][0][1].x + i * metaltracks[layer][0][1].step
                ycord.append((y,layer))
        else:
            for i in range(metaltracks[layer][0][0].num):
                x = metaltracks[layer][0][0].x + i * metaltracks[layer][0][0].step
                xcord.append((x,layer))

    # Step 2: Create vertices only inside the guide rectangles
    for rect in netguide.shapes:
        layer = rect.layer
        if layer == 'li1':
            continue
        for x in xcord:
            for y in ycord:
                if y[1] in checker.adjLayer[x[1]]:
                    if rect.x1 <= x[0] <= rect.x2 and rect.y1 <= y[0] <= rect.y2:
                        key = (x[0], y[0])
                        if key not in grid_map:
                            v = Vertex(x[0], y[0], layer=[layer])
                            grid_map[key] = v
                            listOfVertices.append(v)
                        else:
                            if layer not in grid_map[key]._layer:
                                grid_map[key]._layer.append(layer)

    # Step 3: Connect neighbors (horizontal/vertical)
    for v in listOfVertices:
        x, y = v._xy
        vLayer = v._layer[0]
        hORV = metaltracks[vLayer][1]
        for adjLayer in checker.adjLayer[v._layer[0]]:
            if adjLayer == 'li1':
                continue
            for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                if hORV == 1:
                    neighbor_key = (x + dx * metaltracks.get(adjLayer)[0][0].step,
                                y + dy * metaltracks.get(v._layer[0])[0][1].step)
                else:
                    neighbor_key = (x + dx * metaltracks.get(v._layer[0])[0][0].step,
                                y + dy * metaltracks.get(adjLayer)[0][1].step)
                if neighbor_key in grid_map:
                    for rect in netguide.get_shapes_by_layer(adjLayer):
                        if rect.x1 <= neighbor_key[0] <= rect.x2 and rect.y1 <= neighbor_key[1] <= rect.y2:
                            neighbor = grid_map[neighbor_key]
                            v._nbrs[adjLayer] = v._nbrs.get(adjLayer, []) + [neighbor]

    return grid_map, listOfVertices

def add_path_to_net(path):
    rectList = []
    for i in range(1, len(path)):
        v1 = path[i-1]
        v2 = path[i]
        
        # Determine the layer and width for spacing
        layer1 = v1._layer[0]
        layer2 = v2._layer[0]
        width = checker.layerWidth.get(layer1, 0)  # Default width if layer1 not found
        
        # If layers are different, use the width of the second layer
        if layer1 != layer2:
            width = checker.layerWidth.get(layer2, 0)

        x1, y1 = v1._xy
        x2, y2 = v2._xy
        
        # Adjust for horizontal or vertical spacing
        if y1 == y2:  # Horizontal
            lly = y1 - (width / 2)
            ury = y2 + (width / 2)
            llx, urx = min(x1, x2), max(x1, x2)
        else:  # Vertical
            llx = x1 - (width / 2)
            urx = x2 + (width / 2)
            lly, ury = min(y1, y2), max(y1, y2)
        
        
        # Create the rect and add it to the net
        rect = Rect(llx, lly, urx, ury)
        blockers[v1._layer[0]].append(rect)
        rectList.append(rect)
        # net.addRect(v1._layer[0], llx, lly, urx, ury)
    return rectList

def dummyNodeAddition(gridPoints, srcPoints, endPoints, mettracks):
    sn = Vertex(0, 0, layer=['met1'])
    sn._nbrs['met1'] = []
    for p in srcPoints:
        if p._layer[-1] not in p._nbrs:
            p._nbrs[p._layer[-1]] = []
        p._nbrs[p._layer[-1]].append(sn)
        sn._nbrs['met1'].append(p)
    for sp in srcPoints:
        for gp in gridPoints:
            if gp._layer in sp._layer:
                if mettracks[gp._layer][1] == 1:
                    if gp._xy[1] == sp._xy[1]:
                        sp._nbrs[gp._layer].append(gp)
                else:
                    if gp._xy[0] == sp._xy[0]:
                        sp._nbrs[gp._layer].append(gp)
    for sp in endPoints:
        for gp in gridPoints:
            for l in gp._layer:
                if l in sp._layer:
                    if mettracks[l][1] == 1:
                        if gp._xy[1] == sp._xy[1]:
                            if l in sp._nbrs:
                                sp._nbrs[l].append(gp)
                            else:
                                sp._nbrs[l] = []
                    else:
                        if gp._xy[0] == sp._xy[0]:
                            if l in sp._nbrs:
                                sp._nbrs[l].append(gp)
                            else:
                                sp._nbrs[l] = []

    en = Vertex(0, 0, layer=endPoints[0]._layer)
    en._nbrs[endPoints[0]._layer[0]] = []
    for p in endPoints:
        if p._layer[-1] not in p._nbrs:
            p._nbrs[p._layer[-1]] = []
        p._nbrs[p._layer[-1]].append(en)
        en._nbrs[endPoints[0]._layer[0]].append(p)
    return [sn, en] + srcPoints + endPoints


def pinTrackPoints(rects, metaltracks):
    sol = []
    for layer in rects:
        for rect in rects[layer]:
            for i in range(metaltracks[layer][0][1].num):
                y = metaltracks[layer][0][1].x + i * metaltracks[layer][0][1].step
                if metaltracks[layer][1] == 1:
                    if rect.ur.y <= y and y >= rect.ll.y:
                        sol.append(Vertex(rect.ur.x,y, layer=[layer]))
                else:
                    if rect.ur.x <= y and y >= rect.ll.x:
                        sol.append(Vertex(y, rect.ur.y, layer=[layer]))
    return sol

def portTrackPoints(rects, metaltracks):
    sol = []
    for rect in rects:
        for i in range(metaltracks['met1'][0][1].num):
            y = metaltracks['met1'][0][1].x + i * metaltracks['met1'][0][1].step
            if rect.ur.y <= y and y >= rect.ll.y:
                sol.append(Vertex(rect.ur.x,y, layer=['met1']))
    return sol

###################
def detailed_route(deffile, leffile, guidefile, outdeffile):
    leff = LEFDEFParser.LEFReader()
    checker.layerWidth
    ideff = LEFDEFParser.DEFReader()
    leff.readLEF(leffile)
    lefDict = {m.name() : m for m in leff.macros()}
    ideff.readDEF(deffile)


    insts = {inst.name():checker.Inst(inst, lefDict[inst.macro()]) for inst in ideff.components() if inst.macro() not in checker.skipCells}
    for i in insts:
        for l in insts[i]._obsts:
            blockers[l].extend(insts[i]._obsts[l])


    pins = dict()
    for p in ideff.pins():
        pn = p.name()
        pins[pn] = dict()
        for port in p.ports():
            for layer, rects in port.items():
                if layer not in pins[pn]: pins[pn][layer] = list()
                for r in rects:
                    pins[pn][layer].append(Rect(r.ll.x, r.ll.y, r.ur.x, r.ur.y))

    nets = list()
    idx = 0
    for net in ideff.nets():
        if net.name() not in checker.skipNets:
            nets.append(checker.Net(net, insts, pins, idx))
            idx += 1
    
    ######tracks
    metList = ['met1', 'met2', 'met3', 'met4', 'met5'] 
    mettracks = {}
    mettracks['met1'] =  (ideff.tracks()['met1'],1)
    mettracks['met2'] =  (ideff.tracks()['met2'],0)
    mettracks['met3'] =  (ideff.tracks()['met3'],1)
    mettracks['met4'] =  (ideff.tracks()['met4'],0)
    mettracks['met5'] =  (ideff.tracks()['met5'],1)  #.x .num .step

    ###############src and target points
    possibleEndPoints = {}
    possibleSrcPoints = {}
    for net in nets:
        if list(net._pins.keys())[0][0] == 'PIN':
            possibleEndPoints[net._name] = pinTrackPoints(net._pins[list(net._pins.keys())[0]], mettracks)
        else:
            possibleEndPoints[net._name] = portTrackPoints(net._pins[list(net._pins.keys())[0]]['li1'], mettracks)
        possibleSrcPoints[net._name] = portTrackPoints(net._pins[list(net._pins.keys())[1]]['li1'], mettracks)

    bloatWithX = ideff.gcgrids()[0].step / 2
    bloatWithY = ideff.gcgrids()[1].step / 2
    ##########################
    netguide = parse_shape_file(guidefile)
    for netobj in nets:
        netname = netobj._name
        if netname in netguide:
            bloatedGuide = bloatguideLines(bloatWithX, bloatWithY, netguide[netname])
            grid_map, gridverticesList = gridInsideGuide(mettracks, bloatedGuide)
            srcPoints = possibleSrcPoints[netname]
            tgtPoints = possibleEndPoints[netname]
            verticesList = dummyNodeAddition(gridverticesList, srcPoints, tgtPoints, mettracks)
            finalVList = verticesList + gridverticesList 

            path = astar(finalVList, s=verticesList[0], t=verticesList[1])
            rectList = add_path_to_net(path) 

            for net in ideff.nets():
                if net.name() == netname:
                    for r in rectList:
                        net.addRect(verticesList[0]._layer[0],r)

    ideff.writeDEF("/home/harika/detailedrouter/out.def")
detailed_route('/home/harika/detailedrouter/add5.def', '/home/harika/detailedrouter/sky130.lef', '/home/harika/detailedrouter/add5.guide', '/home/harika/detailedrouter/out.def')