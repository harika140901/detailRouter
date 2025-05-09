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
blockersNoSpace = {}
blockersNoSpace['li1'] = []
blockersNoSpace['met1'] = []
blockersNoSpace['met2'] = []
blockersNoSpace['met3'] = []
blockersNoSpace['met4'] = []
blockersNoSpace['met5'] = []
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
    # Remove the old entry and add a new one
        for i, item in enumerate(self._q):
            if item._xy == v._xy:  # Compare by coordinates
                v._cost = cost
                v._f = v._cost + v._h
                self._q[i] = v
                hq.heapify(self._q)
                return
        # If not found, add it
        v._cost = cost
        v._f = v._cost + v._h
        hq.heappush(self._q, v)


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
        if rects.ur.x >= v._xy[0] and rects.ll.x <= v._xy[0] and rects.ur.y >= v._xy[1] and rects.ll.y <= v._xy[1]:
            b = True
            break
    return b

def path_blocked(v1, v2, layer):
    """Check if the path between v1 and v2 is blocked by any obstacle on the given layer"""
    x1, y1 = v1._xy
    x2, y2 = v2._xy
    
    # For horizontal segments
    if y1 == y2:
        min_x, max_x = min(x1, x2), max(x1, x2)
        for rect in blockers[layer]:
            # Check if blocker overlaps with the path
            if (rect.ll.y <= y1 <= rect.ur.y and 
                not (rect.ur.x <= min_x or rect.ll.x >= max_x)):
                return True
    
    # For vertical segments
    elif x1 == x2:
        min_y, max_y = min(y1, y2), max(y1, y2)
        for rect in blockers[layer]:
            # Check if blocker overlaps with the path
            if (rect.ll.x <= x1 <= rect.ur.x and 
                not (rect.ur.y <= min_y or rect.ll.y >= max_y)):
                return True
    
    return False

def notInsideGuide(v,layer, bloatedGuide):
    b = False
    for rects in bloatedGuide.get_shapes_by_layer(layer):
        if rects.x2 < v._xy[0] or rects.x1 > v._xy[0] or rects.y2 < v._xy[1] or rects.y1 > v._xy[1]:
            b = True
            break
    return b

def validate_path_spacing(v1, v2, layer, spacing, metaltracks):
    """Validate that a path segment maintains proper spacing from all obstacles"""
    x1, y1 = v1._xy
    x2, y2 = v2._xy
    
    layer_direction = metaltracks[layer][1]
    width = layerWidth.get(layer) 
    # For horizontal preferred layers
    if layer_direction == 1:
        lly = y1 - (width / 2)
        ury = y2 + (width / 2)
        llx, urx = min(x1, x2) - (width / 2), max(x1, x2) + (width / 2)
    else:  # Vertical
        llx = x1 - (width / 2)
        urx = x2 + (width / 2)
        lly, ury = min(y1, y2) -  (width / 2), max(y1, y2)+ (width / 2)

        
    # Create the rect and add it to the net
    bloated_path = Rect(int(llx), int(lly), int(urx), int(ury))

    # Check for intersections with any blockers
    for rect in blockers[layer]:
        if (bloated_path.ll.x < rect.ur.x and bloated_path.ur.x > rect.ll.x and
            bloated_path.ll.y < rect.ur.y and bloated_path.ur.y > rect.ll.y):
            return False  # Path violates spacing requirements
    
    return True  # Path is valid

def getAllGridPoints(metaltracks, blockers):
    # Collect all track coordinates for each layer
    x_coords = {}
    y_coords = {}
    
    for layer, (tracks, direction) in metaltracks.items():
        if direction == 1:  # Horizontal tracks (store y-coordinates)
            y_coords[layer] = [tracks[1].x + i * tracks[1].step for i in range(tracks[1].num)]
        else:  # Vertical tracks (store x-coordinates)
            x_coords[layer] = [tracks[0].x + i * tracks[0].step for i in range(tracks[0].num)]
    
    # Create vertices at all valid intersections
    grid_points = []
    grid_map = {}  # (x, y) -> Vertex
    
    horizontalLayers = ['met1', 'met3', 'met5']
    verticalLayers = ['met2', 'met4']
    # For each layer combination
    for layer1 in verticalLayers:
        for layer2 in horizontalLayers:
            # Only process valid layer combinations (adjacent or same)
            if layer2 in checker.adjLayer[layer1] or layer1 == layer2:
                # Get coordinates based on layer directions
                if layer1 in x_coords and layer2 in y_coords:
                    for x in x_coords[layer1]:
                        for y in y_coords[layer2]:
                            # Check if point is inside any blocker
                            if not is_blocked((x, y), [layer1, layer2], blockers):
                                key = (x, y)
                                if key not in grid_map:
                                    v = Vertex(x, y, layer=[layer1, layer2])
                                    grid_map[key] = v
                                    grid_points.append(v)
                                else:
                                    # Add layer if not already present
                                    for l in [layer1, layer2]:
                                        if l not in grid_map[key]._layer:
                                            grid_map[key]._layer.append(l)
    
    # Connect vertices based on their layers and directions
    connectGridPoints(grid_points, grid_map, metaltracks)
    
    return grid_map, grid_points

def is_blocked(point, layers, blockers):
    """Check if a point is inside any blocker for the given layers"""
    x, y = point
    for layer in layers:
        if layer in blockers:
            for rect in blockers[layer]:
                if rect.ll.x <= x <= rect.ur.x and rect.ll.y <= y <= rect.ur.y:
                    return True
    return False


def connectGridPoints(vertices, grid_map, metaltracks):
    """Connect grid points based on layer directions"""
    for v in vertices:
        x, y = v._xy
        
        for layer in v._layer:
            direction = metaltracks[layer][1]
            
            # Initialize neighbor dictionary if needed
            if layer not in v._nbrs:
                v._nbrs[layer] = []
            
            # Check horizontal or vertical neighbors based on layer direction
            if direction == 1:  # Horizontal layer
                # Look for neighbors along x-axis
                step = metaltracks[layer][0][0].step
                for nx in [x - step, x + step]:
                    neighbor_key = (nx, y)
                    if neighbor_key in grid_map:
                        neighbor = grid_map[neighbor_key]
                        if layer in neighbor._layer:
                            v._nbrs[layer].append(neighbor)
            else:  # Vertical layer
                # Look for neighbors along y-axis
                step = metaltracks[layer][0][1].step
                for ny in [y - step, y + step]:
                    neighbor_key = (x, ny)
                    if neighbor_key in grid_map:
                        neighbor = grid_map[neighbor_key]
                        if layer in neighbor._layer:
                            v._nbrs[layer].append(neighbor)

def astar(V, s, t, metaltracks, layerSpacing):
    for v in V:
        v.resetBack()
    def heuristic(current, goals):
        return min(abs(current._xy[0] - g._xy[0]) + abs(current._xy[1] - g._xy[1]) for g in goals)

    for v in V:
        v._h = heuristic(v, t)

    # s._cost = 0
    Q = PriorityQueue(V)
    Q.update(s,0)
    alreadyEvaluated = []
    while not Q.empty():
        u = Q.pop()
        if u in t:
            reached_target = u
            break
        alreadyEvaluated.append(u)
        for layer, neighbors in u._nbrs.items():
            if layer == 'li1':
                continue
            for v in neighbors:
                # Skip if target (will be handled by the break above)
            
                 # Skip if already evaluated
                if v in alreadyEvaluated:
                    continue

                # Skip if path is blocked
                if u._usedLayer is not None:
                    if not validate_path_spacing(u, v, layer, layerSpacing[layer], metaltracks):
                        continue
                    
                # Calculate new cost
                if u == s:
                    gnew = u._cost + (10 if layer not in v._layer else 0)
                else:
                    gnew = u._cost + dist(u, v) + (10 if layer not in v._layer else 0)
                
                # Check layer direction constraints
                valid_direction = False
                if u == s:
                    # Allow any direction from source
                    valid_direction = True
                elif metaltracks[layer][1] == 1:  # Horizontal layer
                    valid_direction = (v._xy[1] == u._xy[1])  # Must be horizontal movement
                else:  # Vertical layer
                    valid_direction = (v._xy[0] == u._xy[0])  # Must be vertical movement
                
                # Only process if direction is valid
                if valid_direction:
                    if v not in Q:
                        Q.push(v)
                    
                    if gnew < v._cost:
                        Q.update(v, gnew)
                        v._parent = u
                        u._child.append(v)
                        v._usedLayer = layer

    path = []
    if reached_target:
        node = reached_target
        while node._parent is not None:
            path.append(node)
            node = node._parent

    
    return path

###############################################################
class Vertex:
    def __init__(self, x, y, cost=math.inf, h=0, child=[], parent=None, layer=[]):
        self._xy = (x, y)
        self._cost = cost
        self._parent = parent
        self._child = []
        self._layer = layer
        self._nbrs = {}
        self._h = h 
        self._f = self._cost + self._h 
        self._usedLayer = None

    def __lt__(self, other):
        return self._f < other._f 

    def __eq__(self, other):
        return self._xy == other._xy and self._usedLayer == other._usedLayer


    def __repr__(self):
        return f'(xy:{self._xy}, cost:{self._cost}, f:{self._f})'
    
    def appendLayer(self, layertoAdd):
        self._layer.append(layertoAdd)
    
    def resetBack(self):
        self._cost = math.inf
        self._parent = None
        self._h = 0
        self._f = self._cost + self._h 
        self._child = []
        self._usedLayer = None

# def addboundaryPINS(listOfVertices): #to metal tracks grid list
#     Vertex(x,y,[])
import copy
def bloatguideLines(bloatWithX, bloatWithY, netguide):
    bloated_guide = copy.deepcopy(netguide)
    for rect in bloated_guide.shapes:
        rect.x1 = rect.x1 - bloatWithX
        rect.x2 = rect.x2 + bloatWithX
        rect.y1 = rect.y1 - bloatWithY
        rect.y2 = rect.y2 + bloatWithY
    return bloated_guide


def gridInsideGuide(metaltracks, netguide):
    xcord = []
    ycord = []
    listOfVertices = []
    grid_map = {}  # (x, y) -> Vertex

    available_layers = set()
    for layer in set(rect.layer for rect in netguide.shapes):
        if layer == 'li1':
            continue
        available_layers.add(layer)

    available_layers = list(available_layers)
    if len(available_layers) >1:
        # Step 1: Collect valid x and y coordinates from metal tracks
        for layer in available_layers:  # layer just to pass one layer at a time
            if metaltracks[layer][1] == 1:
                for i in range(metaltracks[layer][0][1].num):
                    y = metaltracks[layer][0][1].x + i * metaltracks[layer][0][1].step
                    ycord.append((y,layer))
            else:
                for i in range(metaltracks[layer][0][0].num):
                    x = metaltracks[layer][0][0].x + i * metaltracks[layer][0][0].step
                    xcord.append((x,layer))
    elif len(available_layers) == 1:
        for layer in available_layers:  # layer just to pass one layer at a time
            if metaltracks[layer][1] == 1:
                for i in range(metaltracks[layer][0][1].num):
                    y = metaltracks[layer][0][1].x + i * metaltracks[layer][0][1].step
                    ycord.append((y,layer))
                for n in  netguide.get_shapes_by_layer(available_layers[0]):
                    xcord.append((n.x1, layer))
                    xcord.append((n.x1, layer))
                    xcord.append((int((n.x1 + n.x2)/2), layer))
            else:
                for i in range(metaltracks[layer][0][0].num):
                    x = metaltracks[layer][0][0].x + i * metaltracks[layer][0][0].step
                    xcord.append((x,layer))
                for n in  netguide.get_shapes_by_layer(available_layers[0]):
                    ycord.append((n.y1, layer))
                    ycord.append((n.y2, layer))
                    ycord.append((int((n.y1 + n.y2)/2), layer))
    else:
        print('no metal layer guides found for this layer')

    # Step 2: Create vertices only inside the guide rectangles
    for rect in netguide.shapes:
        layer = rect.layer
        if layer == 'li1':
            continue
        for x in xcord:
            for y in ycord:
                if y[1] in checker.adjLayer[x[1]] or y[1] == x[1]:
                    if rect.x1 <= x[0] <= rect.x2 and rect.y1 <= y[0] <= rect.y2:
                        key = (x[0], y[0])
                        if key not in grid_map:
                            v = Vertex(x[0], y[0], layer=[layer])
                            grid_map[key] = v
                            listOfVertices.append(v)
                        else:
                            if layer not in grid_map[key]._layer:
                                grid_map[key]._layer.append(layer)

    # After creating vertices, connect them properly
    for v in listOfVertices:
        x, y = v._xy
        for layer in v._layer:
            hORV = metaltracks[layer][1]
            for adjLayer in [layer] + checker.adjLayer[layer]:
                if adjLayer == 'li1':
                    continue
                # Initialize neighbor dictionary if needed
                if adjLayer not in v._nbrs:
                    v._nbrs[adjLayer] = []
                    
                # Check all four directions
                # Check all four directions
                for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    # Calculate step size based on layer orientation
                    if layer == adjLayer:  # When both layers are the same
                        if hORV == 1:  # Horizontal
                            nx = x + dx * metaltracks.get(layer)[0][0].step
                            ny = y + dy * metaltracks.get(layer)[0][1].step
                        else:  # Vertical
                            nx = x + dx * metaltracks.get(layer)[0][0].step
                            ny = y + dy * metaltracks.get(layer)[0][1].step
                    else:  # Different layers
                        if hORV == 1:  # Horizontal
                            nx = x + dx * metaltracks.get(adjLayer)[0][0].step
                            ny = y + dy * metaltracks.get(layer)[0][1].step
                        else:  # Vertical
                            nx = x + dx * metaltracks.get(layer)[0][0].step
                            ny = y + dy * metaltracks.get(adjLayer)[0][1].step

                        
                    neighbor_key = (nx, ny)
                    if neighbor_key in grid_map:
                        neighbor = grid_map[neighbor_key]
                        # Check if neighbor is in a valid guide for this layer
                        for rect in netguide.get_shapes_by_layer(adjLayer):
                            if rect.x1 <= nx <= rect.x2 and rect.y1 <= ny <= rect.y2:
                                v._nbrs[adjLayer].append(neighbor)
                                break

# Ensure bidirectional connections
    for v in listOfVertices:
        for layer, neighbors in v._nbrs.items():
            for neighbor in neighbors:
                if layer not in neighbor._nbrs:
                    neighbor._nbrs[layer] = []
                if v not in neighbor._nbrs[layer]:
                    neighbor._nbrs[layer].append(v)

    return grid_map, listOfVertices

def add_path_to_net(path, layerWidth, metaltracks):
    path = path[::-1]
    rectList = []
    for i in range(1, len(path)):
        v1 = path[i-1]
        v2 = path[i]
        layer2 = v2._usedLayer
        if v2._usedLayer == None:
            continue
        width = layerWidth.get(layer2) 

        x1, y1 = v1._xy
        x2, y2 = v2._xy
        
        layer_direction = metaltracks[layer2][1]
        
        # For horizontal preferred layers
        if layer_direction == 1:
            lly = y1 - (width / 2)
            ury = y2 + (width / 2)
            llx, urx = min(x1, x2) - (width / 2), max(x1, x2) + (width / 2)
        else:  # Vertical
            llx = x1 - (width / 2)
            urx = x2 + (width / 2)
            lly, ury = min(y1, y2) -  (width / 2), max(y1, y2)+ (width / 2)
        
        
        # Create the rect and add it to the net
        rect = Rect(int(llx), int(lly), int(urx), int(ury))
        rectList.append((rect,v2._usedLayer))
    return rectList

def appendingBlockerswithoutSpaceing(rectList):
    for (rect,layer) in rectList:
        blockersNoSpace[layer].append(rect)

def appendingBlockers(rectList, layerSpacing):
    for (rect,layer) in rectList:
        bloated_rect = Rect(
                int(rect.ll.x - layerSpacing.get(layer)),
                int(rect.ll.y - layerSpacing.get(layer)),
                int(rect.ur.x + layerSpacing.get(layer)),
                int(rect.ur.y + layerSpacing.get(layer))
            )
        blockers[layer].append(bloated_rect)

def dummyNodeAddition(gridPoints, srcPoints, endPoints, mettracks):
    sn = Vertex(0, 0, layer=['met1'])
    # Missing initialization

    # Connect dummy source to all source points
    for p in srcPoints:
        for layer in p._layer:  # Iterate through all layers of the source point
            if layer not in p._nbrs:
                p._nbrs[layer] = []
            p._nbrs[layer].append(sn)
            
            # Make sure the layer exists in sn._nbrs
            if layer not in sn._nbrs:
                sn._nbrs[layer] = []
            sn._nbrs[layer].append(p)

    # For source points, find immediate neighbors on grid
    for sp in srcPoints:
        for l in sp._layer:
            if l == 'li1':
                continue
                
            # Create a dictionary to track closest points in each direction
            closest_left = None
            closest_right = None
            closest_up = None
            closest_down = None
            min_left_dist = float('inf')
            min_right_dist = float('inf')
            min_up_dist = float('inf')
            min_down_dist = float('inf')
            
            for gp in gridPoints:
                if l in gp._layer:
                    # For horizontal tracks
                    if mettracks[l][1] == 1:
                        if gp._xy[1] == sp._xy[1]:  # Same y-coordinate (same track)
                            # Check if point is to the left
                            if gp._xy[0] < sp._xy[0]:
                                dist = sp._xy[0] - gp._xy[0]
                                if dist < min_left_dist:
                                    min_left_dist = dist
                                    closest_left = gp
                            # Check if point is to the right
                            elif gp._xy[0] > sp._xy[0]:
                                dist = gp._xy[0] - sp._xy[0]
                                if dist < min_right_dist:
                                    min_right_dist = dist
                                    closest_right = gp
                    # For vertical tracks
                    else:
                        if gp._xy[0] == sp._xy[0]:  # Same x-coordinate (same track)
                            # Check if point is below
                            if gp._xy[1] < sp._xy[1]:
                                dist = sp._xy[1] - gp._xy[1]
                                if dist < min_down_dist:
                                    min_down_dist = dist
                                    closest_down = gp
                            # Check if point is above
                            elif gp._xy[1] > sp._xy[1]:
                                dist = gp._xy[1] - sp._xy[1]
                                if dist < min_up_dist:
                                    min_up_dist = dist
                                    closest_up = gp
            
            # Connect to closest points in each direction
            if l not in sp._nbrs:
                sp._nbrs[l] = []
                
            # For horizontal tracks, connect left and right
            if mettracks[l][1] == 1:
                if closest_left:
                    sp._nbrs[l].append(closest_left)
                    if l in closest_left._nbrs:
                        closest_left._nbrs[l].append(sp)
                    else:
                        closest_left._nbrs[l] = [sp]
                        
                if closest_right:
                    sp._nbrs[l].append(closest_right)
                    if l in closest_right._nbrs:
                        closest_right._nbrs[l].append(sp)
                    else:
                        closest_right._nbrs[l] = [sp]
            # For vertical tracks, connect up and down
            else:
                if closest_up:
                    sp._nbrs[l].append(closest_up)
                    if l in closest_up._nbrs:
                        closest_up._nbrs[l].append(sp)
                    else:
                        closest_up._nbrs[l] = [sp]
                        
                if closest_down:
                    sp._nbrs[l].append(closest_down)
                    if l in closest_down._nbrs:
                        closest_down._nbrs[l].append(sp)
                    else:
                        closest_down._nbrs[l] = [sp]
    
    # Do the same for end points
    for sp in endPoints:
        for l in sp._layer:
            if l == 'li1':
                continue
                
            # Create a dictionary to track closest points in each direction
            closest_left = None
            closest_right = None
            closest_up = None
            closest_down = None
            min_left_dist = float('inf')
            min_right_dist = float('inf')
            min_up_dist = float('inf')
            min_down_dist = float('inf')
            
            for gp in gridPoints:
                if l in gp._layer:
                    # For horizontal tracks
                    if mettracks[l][1] == 1:
                        if gp._xy[1] == sp._xy[1]:  # Same y-coordinate (same track)
                            # Check if point is to the left
                            if gp._xy[0] < sp._xy[0]:
                                dist = sp._xy[0] - gp._xy[0]
                                if dist < min_left_dist:
                                    min_left_dist = dist
                                    closest_left = gp
                            # Check if point is to the right
                            elif gp._xy[0] > sp._xy[0]:
                                dist = gp._xy[0] - sp._xy[0]
                                if dist < min_right_dist:
                                    min_right_dist = dist
                                    closest_right = gp
                    # For vertical tracks
                    else:
                        if gp._xy[0] == sp._xy[0]:  # Same x-coordinate (same track)
                            # Check if point is below
                            if gp._xy[1] < sp._xy[1]:
                                dist = sp._xy[1] - gp._xy[1]
                                if dist < min_down_dist:
                                    min_down_dist = dist
                                    closest_down = gp
                            # Check if point is above
                            elif gp._xy[1] > sp._xy[1]:
                                dist = gp._xy[1] - sp._xy[1]
                                if dist < min_up_dist:
                                    min_up_dist = dist
                                    closest_up = gp
            
            # Connect to closest points in each direction
            if l not in sp._nbrs:
                sp._nbrs[l] = []
                
            # For horizontal tracks, connect left and right
            if mettracks[l][1] == 1:
                if closest_left and closest_left not in sp._nbrs[l]:
                    sp._nbrs[l].append(closest_left)
                    if l in closest_left._nbrs:
                        if sp not in closest_left._nbrs[l]:
                            closest_left._nbrs[l].append(sp)
                    else:
                        closest_left._nbrs[l] = [sp]
                        
                if closest_right and closest_right not in sp._nbrs[l]:
                    sp._nbrs[l].append(closest_right)
                    if l in closest_right._nbrs:
                        if sp not in closest_right._nbrs[l]:
                            closest_right._nbrs[l].append(sp)
                    else:
                        closest_right._nbrs[l] = [sp]
            # For vertical tracks, connect up and down
            else:
                if closest_up and closest_up not in sp._nbrs[l]:
                    sp._nbrs[l].append(closest_up)
                    if l in closest_up._nbrs:
                        if sp not in closest_up._nbrs[l]:
                            closest_up._nbrs[l].append(sp)
                    else:
                        closest_up._nbrs[l] = [sp]
                        
                if closest_down and closest_down not in sp._nbrs[l]:
                    sp._nbrs[l].append(closest_down)
                    if l in closest_down._nbrs:
                        if sp not in closest_down._nbrs[l]:
                            closest_down._nbrs[l].append(sp)
                    else:
                        closest_down._nbrs[l] = [sp]
    
        # Add this at the end of dummyNodeAddition
    for v in gridPoints + srcPoints + endPoints + [sn]:
        for layer, neighbors in v._nbrs.items():
            for neighbor in neighbors:
                if layer not in neighbor._nbrs:
                    neighbor._nbrs[layer] = []
                if v not in neighbor._nbrs[layer]:
                    neighbor._nbrs[layer].append(v)

    return sn, srcPoints, endPoints

def pinTrackPoints(rects, metaltracks, bloatGuides):
    sol = []
    
    for layer in rects:
        # Get list of adjacent layers based on direction
        adj_layers = checker.adjLayer[layer]
        if layer == 'li1':
            layer = adj_layers[0]
        if 'li1' in adj_layers:
            adj_layers.remove('li1')
        for rect in rects[layer]:
            # Process the original layer
            if metaltracks[layer][1] == 1:  # Horizontal layer
                # Get y-coordinates from the horizontal layer
                all_y_coords = [metaltracks[layer][0][1].x + i * metaltracks[layer][0][1].step
                               for i in range(metaltracks[layer][0][1].num)]
                
                intersecting_y = [y for y in all_y_coords if rect.ll.y <= y <= rect.ur.y]
                
                # Get x-coordinates from adjacent vertical layers
                for adj_layer in adj_layers:
                    if layer != adj_layer:
                        if metaltracks[adj_layer][1] == 0:  # Vertical layer
                            all_x_coords = [metaltracks[adj_layer][0][0].x + i * metaltracks[adj_layer][0][0].step
                                        for i in range(metaltracks[adj_layer][0][0].num)]
                            
                            intersecting_x = [x for x in all_x_coords if rect.ll.x <= x <= rect.ur.x]
                            
                            # Create vertices at all intersections
                            for x in intersecting_x:
                                for y in intersecting_y:
                                    # Create vertex with both layers
                                    sol.append(Vertex(x, y, layer=[layer, adj_layer]))
                
                # Also add edge points on the original layer
                for y in intersecting_y:
                    sol.append(Vertex(rect.ur.x, y, layer=[layer]))
                    sol.append(Vertex(rect.ll.x, y, layer=[layer]))
                    sol.append(Vertex(int(rect.ll.x + rect.ur.x)/2, y, layer=[layer]))
            
            else:  # Vertical layer
                # Get x-coordinates from the vertical layer
                all_x_coords = [metaltracks[layer][0][0].x + i * metaltracks[layer][0][0].step
                               for i in range(metaltracks[layer][0][0].num)]
                
                intersecting_x = [x for x in all_x_coords if rect.ll.x <= x <= rect.ur.x]
                
                # Get y-coordinates from adjacent horizontal layers
                for adj_layer in adj_layers:
                    if layer != adj_layer:
                        if metaltracks[adj_layer][1] == 1:  # Horizontal layer
                            all_y_coords = [metaltracks[adj_layer][0][1].x + i * metaltracks[adj_layer][0][1].step
                                        for i in range(metaltracks[adj_layer][0][1].num)]
                            
                            intersecting_y = [y for y in all_y_coords if rect.ll.y <= y <= rect.ur.y]
                            
                            # Create vertices at all intersections
                            for x in intersecting_x:
                                for y in intersecting_y:
                                    # Create vertex with both layers
                                    sol.append(Vertex(x, y, layer=[layer, adj_layer]))
                
                # Also add edge points on the original layer
                for x in intersecting_x:
                    sol.append(Vertex(x, rect.ur.y, layer=[layer]))
                    sol.append(Vertex(x, rect.ll.y, layer=[layer]))
                    sol.append(Vertex(x, int(rect.ll.y + rect.ur.y)/2, layer=[layer]))
    
    return sol

###################
layerWidth = dict()
layerSpacing = dict()


def detailed_route(deffile, leffile, guidefile, outdeffile):
    
    leff = LEFDEFParser.LEFReader()
    ideff = LEFDEFParser.DEFReader()
    leff.readLEF(leffile)
    lefDict = {m.name() : m for m in leff.macros()}
    ideff.readDEF(deffile)

    for layer in leff.layers():
        layerWidth[layer.name()] = layer.width()
        layerSpacing[layer.name()] = layer.pitch() - layer.width()

    insts = {inst.name():checker.Inst(inst, lefDict[inst.macro()]) for inst in ideff.components() if inst.macro() not in checker.skipCells}
    for i in insts:
        for l in insts[i]._obsts:
            for rect in insts[i]._obsts[l]:
                bloated_rect = Rect(
                int(rect.ll.x - layerSpacing.get(l)),
                int(rect.ll.y - layerSpacing.get(l)),
                int(rect.ur.x + layerSpacing.get(l)),
                int(rect.ur.y + layerSpacing.get(l)))
                blockers[l].append(bloated_rect)

    pins = dict()
    for p in ideff.pins():
        pn = p.name()
        pins[pn] = dict()
        for port in p.ports():
            for layer, rects in port.items():
                if layer not in pins[pn]: pins[pn][layer] = list()
                for r in rects:
                    pins[pn][layer].append(Rect(int(r.ll.x), int(r.ll.y), int(r.ur.x), int(r.ur.y)))

    nets = list()
    idx = 0
    b = False
    for net in ideff.nets():
        if net.name() not in checker.skipNets:
            if any(skip in net.name() for skip in checker.skipNets):
                continue
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
    bloatWithX = ideff.gcgrids()[0].step 
    bloatWithY = ideff.gcgrids()[1].step 
    ##########################
    netguide = parse_shape_file(guidefile)
    
    net_lengths = []
    for netobj in nets:
        netname = netobj._name
        if netname in netguide:
            bloatedGuide = bloatguideLines(bloatWithX, bloatWithY, netguide[netname])
            
            # Calculate minimum distance between any two pins as the netlength
            min_netlength = float('inf')
            pin_keys = list(netobj._pins.keys())
            
            if len(pin_keys) >= 2:
                for i in range(len(pin_keys)):
                    src_points = pinTrackPoints(netobj._pins[pin_keys[i]], mettracks, bloatedGuide)
                    for j in range(i+1, len(pin_keys)):
                        dst_points = pinTrackPoints(netobj._pins[pin_keys[j]], mettracks, bloatedGuide)
                        
                        for src in src_points:
                            for dst in dst_points:
                                distance = abs(src._xy[0] - dst._xy[0]) + abs(src._xy[1] - dst._xy[1])
                                min_netlength = min(min_netlength, distance)
            
            if min_netlength != float('inf'):
                net_lengths.append((netobj, min_netlength))
    
    # Sort nets by netlength (shortest first)
    net_lengths.sort(key=lambda x: x[1])
    # Process nets in order of increasing netlength
    for netobj, _ in net_lengths:
        netname = netobj._name
        if netname in netguide:
            bloatedGuide = bloatguideLines(bloatWithX, bloatWithY, netguide[netname])
            grid_map, gridverticesList = gridInsideGuide(mettracks, bloatedGuide)
            
            # Get all pins for this net
            pin_keys = list(netobj._pins.keys())
            
            # If there are only 2 pins, handle as before
            # Replace the pin connection logic with a single loop approach
            if len(pin_keys) >= 2:
                # Start with the first two pins
                currentEndPoints = pinTrackPoints(netobj._pins[pin_keys[0]], mettracks, bloatedGuide)
                currentSrcPoints = pinTrackPoints(netobj._pins[pin_keys[1]], mettracks, bloatedGuide)
                
                s, currentSrcPoints, currentEndPoints = dummyNodeAddition(gridverticesList, currentSrcPoints, currentEndPoints, mettracks)
                finalVList = [s] + currentSrcPoints + currentEndPoints + gridverticesList
                
                firstPath = astar(finalVList, s=s, t=currentEndPoints, metaltracks=mettracks, layerSpacing=layerSpacing)
                
                if len(firstPath) == 0:
                    for pt in currentEndPoints:
                        pt._usedLayer = None
                    for pt in currentSrcPoints:
                        pt._usedLayer = None
                    grid_map, gridverticesList = getAllGridPoints(mettracks, blockers)
                    s, currentSrcPoints, currentEndPoints = dummyNodeAddition(gridverticesList, currentSrcPoints, currentEndPoints, mettracks)
                    finalVList = [s] + currentSrcPoints + currentEndPoints + gridverticesList
                    firstPath = astar(finalVList, s=s, t=currentEndPoints, metaltracks=mettracks, layerSpacing=layerSpacing)
                finalPath = firstPath
                if len(finalPath) == 0:
                        print(f"Warning: Failed to find path for {netname} using guide-based routing. Trying global routing...")
                allRectLists = []
                currentRectList = add_path_to_net(firstPath, layerWidth, mettracks)
                allRectLists.extend(currentRectList)
                
                # Initialize combined starting points for subsequent iterations
                combinedStartPoints = currentSrcPoints.copy()
                
                # Add points from the first path solution
                layer_to_rects = defaultdict(list)
                for rect, layer in currentRectList:
                    layer_to_rects[layer].append(rect)
                
                additionalPoints = pinTrackPoints(layer_to_rects, mettracks, bloatedGuide)
                combinedStartPoints.extend(additionalPoints)
                
                # Connect remaining pins incrementally
                for i in range(2, len(pin_keys)):
                    nextEndPoints = pinTrackPoints(netobj._pins[pin_keys[i]], mettracks, bloatedGuide)
                    
                    s, combinedStartPoints, nextEndPoints = dummyNodeAddition(gridverticesList, combinedStartPoints, nextEndPoints, mettracks)
                    finalVList = [s] + combinedStartPoints + nextEndPoints + gridverticesList
                    
                    nextPath = astar(finalVList, s=s, t=nextEndPoints, metaltracks=mettracks, layerSpacing=layerSpacing)
                    
                    if len(nextPath) == 0:
                        for pt in nextEndPoints:
                            pt._usedLayer = None 
                        for pt in combinedStartPoints:
                            pt._usedLayer = None
                        grid_map, gridverticesList = getAllGridPoints(mettracks, blockers)
                        s, combinedStartPoints, nextEndPoints = dummyNodeAddition(gridverticesList, combinedStartPoints, nextEndPoints, mettracks)
                        finalVList = [s] + combinedStartPoints + nextEndPoints + gridverticesList
                        nextPath = astar(finalVList, s=s, t=nextEndPoints, metaltracks=mettracks, layerSpacing=layerSpacing)
                    finalPath = finalPath + nextPath
                    if len(finalPath) == 0:
                        print(f"Warning: Failed to find path for {netname} using guide-based routing. Trying global routing...")
                    nextRectList = add_path_to_net(nextPath, layerWidth, mettracks)
                    allRectLists.extend(nextRectList)
                    
                    # Update starting points for next iteration
                    layer_to_rects = defaultdict(list)
                    for rect, layer in nextRectList:
                        layer_to_rects[layer].append(rect)
                    
                    additionalPoints = pinTrackPoints(layer_to_rects, mettracks, bloatedGuide)
                    combinedStartPoints.extend(additionalPoints)
                
                # Add all blockers at once after routing is complete
                appendingBlockers(allRectLists, layerSpacing)
                print(netname, finalPath)
                # Add all rects to DEF
                for n in ideff.nets():
                    if n.name() == netname:
                        for r, l in allRectLists:
                            n.addRect(l, int(r.ll.x), int(r.ll.y), int(r.ur.x), int(r.ur.y))


    ideff.writeDEF(outdeffile)
detailed_route('/home/harika/detailedrouter/add5.def', '/home/harika/detailedrouter/sky130.lef', '/home/harika/detailedrouter/add5.guide', '/home/harika/detailedrouter/out.def')
