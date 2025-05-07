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
    
    # Create a bloated rectangle representing the path with proper spacing
    # if y1 == y2:  # Horizontal segment
    #     bloated_path = Rect(
    #         int(min(x1, x2) - spacing),
    #         int(y1 - spacing),
    #         int(max(x1, x2) + spacing),
    #         int(y1 + spacing)
    #     )
    # else:  # Vertical segment
    #     bloated_path = Rect(
    #         int(x1 - spacing),
    #         int(min(y1, y2) - spacing),
    #         int(x1 + spacing),
    #         int(max(y1, y2) + spacing)
    #     )
    
    # if y1 == y2:  # Horizontal segment
    #     bloated_path = Rect(
    #         int(min(x1, x2)),
    #         int(y1),
    #         int(max(x1, x2)),
    #         int(y1)
    #     )
    # else:  # Vertical segment
    #     bloated_path = Rect(
    #         int(x1),
    #         int(min(y1, y2)),
    #         int(x1),
    #         int(max(y1, y2))
    #     )
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

def astar(V, s, t, bloatedGuide, metaltracks, layerSpacing, guideCheck = True):
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
    p=0
    if guideCheck:
        guidecheck = True
    else:
        guidecheck = False
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
                if v in t:
                    guidecheck = False
                    
                # Skip if path is blocked
                if u._usedLayer is not None:
                    if not validate_path_spacing(u, v, layer, layerSpacing[layer], metaltracks):
                        continue
                
                # Skip if outside guide
                if notInsideGuide(v, layer, bloatedGuide) and guidecheck:
                    continue
                    
                # Skip if already evaluated
                if v in alreadyEvaluated:
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
                if guideCheck:
                    guidecheck = True

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
            else:
                for i in range(metaltracks[layer][0][0].num):
                    x = metaltracks[layer][0][0].x + i * metaltracks[layer][0][0].step
                    xcord.append((x,layer))
                for n in  netguide.get_shapes_by_layer(available_layers[0]):
                    ycord.append((n.y1, layer))
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
                for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                    # Calculate step size based on layer orientation
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
    sn._nbrs['met1'] = []
    
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
    
    return sn, srcPoints, endPoints

def pinTrackPoints(rects, metaltracks, bloatGuides):
    sol = []
    
    for layer in rects:
        if layer == 'li1':
            metaltrackslayertocheck = 'met1'
        else:
            metaltrackslayertocheck = layer
            
        for rect in rects[layer]:
            if metaltracks[metaltrackslayertocheck][1] == 1:
                all_y_coords = [metaltracks[metaltrackslayertocheck][0][1].x + i * metaltracks[metaltrackslayertocheck][0][1].step 
                               for i in range(metaltracks[metaltrackslayertocheck][0][1].num)]
                
                intersecting_tracks = [y for y in all_y_coords if rect.ll.y <= y <= rect.ur.y]
                
                for y in intersecting_tracks:
                    sol.append(Vertex(rect.ur.x, y, layer=[metaltrackslayertocheck]))

            else:
                all_x_coords = [metaltracks[metaltrackslayertocheck][0][0].x + i * metaltracks[metaltrackslayertocheck][0][0].step 
                               for i in range(metaltracks[metaltrackslayertocheck][0][0].num)]

                intersecting_tracks = [x for x in all_x_coords if rect.ll.x <= x <= rect.ur.x]
                
                for x in intersecting_tracks:
                    sol.append(Vertex(x, rect.ur.y, layer=[metaltrackslayertocheck]))
    
    # Add layer information from bloatGuides
    for s in sol:
        for rect in bloatGuides.shapes:
            if rect.x2 > s._xy[0] and rect.x1 < s._xy[0] and rect.y2 > s._xy[1] and rect.y1 < s._xy[1]:
                if rect.layer not in s._layer:
                    if rect.layer == 'li1':
                        s._layer.append('met1')
                    else:
                        s._layer.append(rect.layer)
    
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
    bloatWithX = ideff.gcgrids()[0].step / 2
    bloatWithY = ideff.gcgrids()[1].step / 2
    ##########################
    netguide = parse_shape_file(guidefile)
    print(len(nets))
    for netobj in nets:
        netname = netobj._name
        if netname in netguide:
            bloatedGuide = bloatguideLines(bloatWithX, bloatWithY, netguide[netname])
            grid_map, gridverticesList = gridInsideGuide(mettracks, bloatedGuide)
            
            # Get all pins for this net
            pin_keys = list(netobj._pins.keys())
            
            # If there are only 2 pins, handle as before
            if len(pin_keys) == 2:
                tgtPoints = pinTrackPoints(netobj._pins[pin_keys[0]], mettracks, bloatedGuide)
                srcPoints =  pinTrackPoints(netobj._pins[pin_keys[1]], mettracks, bloatedGuide)
                
                s, srcPoints, tgtPoints = dummyNodeAddition(gridverticesList, srcPoints, tgtPoints, mettracks)
                finalVList = [s] + srcPoints + tgtPoints + gridverticesList
                path = astar(finalVList, s=s, t=tgtPoints, bloatedGuide=bloatedGuide, metaltracks=mettracks, layerSpacing=layerSpacing)
                
                if len(path) == 0:
                    grid_map, gridverticesList = getAllGridPoints(mettracks, blockers)
                    s, srcPoints, tgtPoints = dummyNodeAddition(gridverticesList, srcPoints, tgtPoints, mettracks)
                    finalVList = [s] + srcPoints + tgtPoints + gridverticesList
                    path = astar(finalVList, s=s, t=tgtPoints, bloatedGuide=bloatedGuide, metaltracks=mettracks, layerSpacing=layerSpacing, guideCheck=False)
                print(netname, path)
                rectList = add_path_to_net(path, layerWidth, mettracks)
                appendingBlockers(rectList, layerSpacing)
                
                # Add rects to DEF
                for n in ideff.nets():
                    if n.name() == netname:
                        for r, l in rectList:
                            n.addRect(l, int(r.ll.x), int(r.ll.y), int(r.ur.x), int(r.ur.y))
            
            # If there are 3 or more pins, handle incrementally
            elif len(pin_keys) >= 3:
                # Connect first two pins
                firstEndPoints = pinTrackPoints(netobj._pins[pin_keys[0]], mettracks, bloatedGuide)
                firstSrcPoints = pinTrackPoints(netobj._pins[pin_keys[1]], mettracks, bloatedGuide)
                
                s, firstSrcPoints, firstEndPoints = dummyNodeAddition(gridverticesList, firstSrcPoints, firstEndPoints, mettracks)
                finalVList = [s] + firstSrcPoints + firstEndPoints + gridverticesList
                firstPath = astar(finalVList, s=s, t=firstEndPoints, bloatedGuide=bloatedGuide, metaltracks=mettracks, layerSpacing=layerSpacing)
                firstRectList = add_path_to_net(firstPath, layerWidth, mettracks)
                
                layer_to_rects = defaultdict(list)

                for rect, layer in firstRectList:
                    layer_to_rects[layer].append(rect)
                
                # Create additional starting points from the first path
                additionalStartPoints = []
                additionalPoints = pinTrackPoints(layer_to_rects, mettracks, bloatedGuide)
                additionalStartPoints.extend(additionalPoints)
                
                # Connect to the third pin
                if pin_keys[2][0] == 'PIN':
                    thirdEndPoints = pinTrackPoints(netobj._pins[pin_keys[2]], mettracks, bloatedGuide)
                else:
                    thirdEndPoints = pinTrackPoints(netobj._pins[pin_keys[2]], mettracks, bloatedGuide)
                
                # Combine original starting points with points from first solution
                combinedStartPoints = firstSrcPoints + additionalStartPoints
                
                # Route from combined starting points to third pin
                s, combinedStartPoints, thirdEndPoints = dummyNodeAddition(gridverticesList, combinedStartPoints, thirdEndPoints, mettracks)
                finalVList = [s] + combinedStartPoints + thirdEndPoints + gridverticesList
                secondPath = astar(finalVList, s=s, t=thirdEndPoints, bloatedGuide=bloatedGuide, metaltracks=mettracks, layerSpacing=layerSpacing)
                print(netname,firstPath + secondPath)
                secondRectList = add_path_to_net(secondPath, layerWidth, mettracks)
                
                # Combine both solutions
                combinedRectList = firstRectList + secondRectList
                appendingBlockers(combinedRectList, layerSpacing)
                
                # Add all rects to DEF
                for n in ideff.nets():
                    if n.name() == netname:
                        for r, l in combinedRectList:
                            n.addRect(l, int(r.ll.x), int(r.ll.y), int(r.ur.x), int(r.ur.y))
            

    ideff.writeDEF("/home/harika/detailedrouter/out.def")
detailed_route('/home/harika/detailedrouter/add5.def', '/home/harika/detailedrouter/sky130.lef', '/home/harika/detailedrouter/add5.guide', '/home/harika/detailedrouter/out.def')