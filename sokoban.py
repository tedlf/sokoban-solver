#-----------------------------------------------------------------------------------------
# Use Python 3
# Suggested font: Menlo Regular
#-----------------------------------------------------------------------------------------

import copy
import itertools
import os
import queue
import random
import sys
import termios
import time
import tty
from datetime import datetime
from io import StringIO
from optparse import OptionParser


#-----------------------------------------------------------------------------------------
# Constants
#-----------------------------------------------------------------------------------------
PURPLE = '\033[95m'
CYAN = '\033[96m'
DARKCYAN = '\033[36m'
BLUE = '\033[94m'
GREEN = '\033[92m'
YELLOW = '\033[93m'
RED = '\033[91m'
BOLD = '\033[1m'
UNDERLINE = '\033[4m'
END = '\033[0m'

# COLOR_NC = '\e[0m' # No Color
# COLOR_WHITE = '\e[1;37m'
# COLOR_BLACK = '\e[0;30m'
# COLOR_BLUE = '\e[0;34m'
# COLOR_LIGHT_BLUE = '\e[1;34m'
# COLOR_GREEN = '\e[0;32m'
# COLOR_LIGHT_GREEN = '\e[1;32m'
# COLOR_CYAN = '\e[0;36m'
# COLOR_LIGHT_CYAN = '\e[1;36m'
# COLOR_RED = '\e[0;31m'
# COLOR_LIGHT_RED = '\e[1;31m'
# COLOR_PURPLE = '\e[0;35m'
# COLOR_LIGHT_PURPLE = '\e[1;35m'
# COLOR_BROWN = '\e[0;33m'
# COLOR_YELLOW = '\e[1;33m'
# COLOR_GRAY = '\e[0;30m'
# COLOR_LIGHT_GRAY = '\e[0;37m'

# For Python 3
# References:
#  - http://www.unicode.org/charts/beta/nameslist/n_25A0.html
#  - https://en.wikipedia.org/wiki/Geometric_Shapes
LARGE_WHITE_SQUARE                  = '\u2b1c'
WHITE_SQUARE                        = '\u25a1'
WHITE_SQUARE_WITH_ROUNDED_CORNERS   = '\u25a2'
WHITE_SQUARE_ENCLOSING              = '\u20de'
WHITE_MEDIUM_SQUARE                 = '\u25fb'
BULLS_EYE                           = '\u25CE'
WHITE_UP_POINTING_TRIANGLE          = '\u25B3'
WHITE_UP_POINTING_TRIANGLE_WITH_DOT = '\u25EC'
SMALL_DELTA                         = '\u03B4'

# WALL = LARGE_WHITE_SQUARE
# TARGET = GREEN + BULLS_EYE + END
# BOX = RED + WHITE_UP_POINTING_TRIANGLE + END
# BOX_ON_TARGET = RED + WHITE_UP_POINTING_TRIANGLE_WITH_DOT + END
# PERSON = BLUE + SMALL_DELTA + END
# PERSON_ON_TARGET = UNDERLINE + BLUE + SMALL_DELTA + END

EMPTY_BOARD_EQUIVALENT = {
    'P': ' ',
    'p': 'T',
    'B': ' ',
    'b': 'T',
    'T': 'T',
    'W': 'W',
    ' ': ' ',
}

DISPLAY_TEXT = {
    # Editor Mode
    True: {
        'P': SMALL_DELTA,
        'p': UNDERLINE + SMALL_DELTA + END,
        'B': WHITE_UP_POINTING_TRIANGLE,
        'b': WHITE_UP_POINTING_TRIANGLE_WITH_DOT,
        'T': BULLS_EYE,
        'W': WHITE_MEDIUM_SQUARE,
    },
    # Not Editor Mode
    False: {
        'P': BLUE + SMALL_DELTA + END,
        'p': UNDERLINE + BLUE + SMALL_DELTA + END,
        'B': RED + WHITE_UP_POINTING_TRIANGLE + END,
        'b': RED + WHITE_UP_POINTING_TRIANGLE_WITH_DOT + END,
        'T': GREEN + BULLS_EYE + END,
        'W': WHITE_MEDIUM_SQUARE,
    },
}

# Directions
U = 0, -1
R = 1, 0
D = 0, 1
L = -1, 0

DIRECTION_NAME = {
    (0, -1): 'U',
    (1, 0): 'R',
    (0, 1): 'D',
    (-1, 0): 'L',
}

DIRECTION = {
    'U': U,
    'R': R,
    'D': D,
    'L': L,
}

KEY_DIRECTION = {
    65: U,
    66: D,
    67: R,
    68: L,
}

# Includes Dvorkak keyboard equivalents.
USER_KEYS = ('u', 'g', 'q', "'", 'r', 'p')
EDITOR_KEYS = ('u', 'g', 'q', "'", 'w', ',', ' ', 't', 'y', 'b', 'x', 'p', 'l', 's', 'o')


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def enable_echo():
    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)
    old[3] = old[3] | termios.ECHO
    termios.tcsetattr(fd, termios.TCSADRAIN, old)


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def get_user_input(prompt, opts):
    enable_echo()
    input_text = input(prompt)
    if opts.user or opts.edit:
        tty.setcbreak(sys.stdin)

    return input_text


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
class State():
    def __init__(self, *args):
        # Expected arguments: person, boxes, history
        if len(args) == 3:
            self.person = args[0]
            self.boxes = args[1]
            self.history = args[2]
        # Expected arguments: board, full_description
        elif len(args) == 2:
            self.person = args[0].board_position(args[1][0])
            self.boxes = [args[0].board_position(b) for b in args[1][1:-1]]
            self.history = args[1][-1]
        # Default
        else:
            self.person = (0, 0)
            self.boxes = []
            self.history = []

    def signature(self):
        return hash(tuple([self.person] + sorted(self.boxes)))

    def raw_signature(self):
        return tuple([self.person] + sorted(self.boxes))

    def full_description(self, board):
        return tuple([board.single_index(self.person)] + sorted(board.single_index(b) for b in self.boxes) + [self.history])

    def __eq__(self, other):
        return self.signature == other.signature

    def __str__(self):
        return '{} {}'.format(self.person, self.boxes)


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
class Board():
    def __init__(self, NX, NY, raw_board, empty_board, targets, walls):
        self.NX = NX
        self.NY = NY
        self.raw_board = raw_board
        self.empty_board = empty_board
        self.targets = targets
        self.walls = walls
        # if NX * NY <= 256:
        #     self.compression_type = SINGLE
        # elif reachable spaces <= 256:
        #     self.compression_type = DICTIONARY
        #     , use dictionary
        # elif NX <= 256 and NY <= 256:
        #     self.compression_type = DOUBLE
        # elif reachable spaces:
        #     self.compression_type = SINGLE
        # else:
        #     self.compression_type = NO_COMPRESSION

    # Returns a single integer index for p, for a board layout that is a single array.
    def single_index(self, p):
        return p[0] + self.NX * p[1]

    # Returns a position tuple (x, y) for the single integer position "i".
    def board_position(self, i):
        return (i % self.NX, i // self.NX)

    # Test whether a position is inside the board boundaries.
    def inbounds(self, p):
        return 0 <= p[0] and p[0] < self.NX and 0 <= p[1] and p[1] < self.NY

    # Test whether a position is inbounds and not a wall.
    def legal_position(self, p):
        return self.inbounds(p) and p not in self.walls

    # Test whether a position is out of bounds or a wall.
    def illegal_position(self, p):
        return not self.legal_position(p)

    # Test whether a box is immobile in the direction perpendicular to the input direction 'dir'.
    def immobile_perp(self, dir, box):
        return self.illegal_position(move(box, rotate(1, dir))) or self.illegal_position(move(box, rotate(-1, dir)))

    # Test whether a position is a corner.
    def is_corner(self, p):
        return (self.illegal_position(move(p, U)) or self.illegal_position(move(p, D))) and \
            (self.illegal_position(move(p, L)) or self.illegal_position(move(p, R)))

    # Check whether or not a move will be a dead end. This check is not exhaustive (yet!).
    def dead_end(self, dir, box, boxes):

        # Check for box in corner.
        if box not in self.targets and move(box, dir) in self.walls and self.immobile_perp(dir, box):
            return True

        # Check for an immobile pair.
        for dir2 in U, R, D, L:
            pos2 = move(box, dir2)
            if pos2 in boxes and (box not in self.targets or pos2 not in self.targets) and self.immobile_perp(dir2, box) and self.immobile_perp(dir2, pos2):
                return True

        # Check for an immobile 2 x 2 square consisting of boxes and walls.
        for turn in 1, -1:
            new_pos, new_direction = box, dir
            square, number_targets, number_boxes = 0, 0, 0
            while square < 4 and (new_pos in boxes or new_pos in self.walls):
                new_pos, new_direction = move(new_pos, new_direction), rotate(turn, new_direction)
                if new_pos in boxes:
                    number_boxes += 1
                if new_pos in self.targets:
                    number_targets += 1
                square += 1
            if square == 4 and number_targets != number_boxes:
                return True

        # Check for two boxes that can only be moved into a corner.
        for dir2 in U, R, D, L:
            if self.immobile_perp(dir2, box):
                possible_corner = move(box, dir2)
                if self.is_corner(possible_corner):
                    for turn in 1, -1:
                        dir3 = rotate(turn, dir2)
                        pos2 = move(possible_corner, dir3)
                        if pos2 in boxes and self.immobile_perp(dir3, pos2):
                            number_targets = sum(p in self.targets for p in [box, possible_corner, pos2])
                            if number_targets < 2:
                                return True

        # Check for a box that is stuck against a wall.
        if self.illegal_position(move(box, dir)):
            number_targets = int(box in self.targets)
            number_boxes = 1
            for turn in 1, -1:
                dir2 = rotate(turn, dir)
                pos_along_wall = move(box, dir2)
                while self.legal_position(pos_along_wall):
                    if not self.immobile_perp(dir2, pos_along_wall):
                        return False
                    if pos_along_wall in self.targets:
                        number_targets += 1
                    if pos_along_wall in boxes:
                        number_boxes += 1
                    pos_along_wall = move(pos_along_wall, dir2)
            if number_targets < number_boxes:
                return True

        return False

    # Print the current board and state.
    def print_current(self, state, text_output, summary_output, clear_screen=True, editor_mode=False):
        if not editor_mode:
            display_board = self.empty_board.copy()
            if state.person in self.targets:
                display_board[state.person] = 'p'
            else:
                display_board[state.person] = 'P'
            for box in state.boxes:
                if display_board[box] == 'T':
                    display_board[box] = 'b'
                else:
                    display_board[box] = 'B'
        else:
            display_board = self.raw_board.copy()
            display_board[state.person] = UNDERLINE + YELLOW + display_board[state.person] + END
        output = StringIO()
        if clear_screen:
            output.write('\033c\n')

        if summary_output is None:
            output.write('\n')
        elif isinstance(summary_output, int):
            output.write('Move: {}\n\n'.format(summary_output))
        elif len(summary_output) == 2 and editor_mode:
            output.write('Boxes: {}  Targets: {}\n\n'.format(*summary_output))
        elif len(summary_output) == 2:
            output.write('Move: {}  Pushes: {}\n\n'.format(*summary_output))
        elif len(summary_output) == 3:
            output.write('Depth: {:,}  Queue: {:,}  Visited: {:,}\n\n'.format(*summary_output))
        elif len(summary_output) == 4:
            output.write('Time: {}  Depth: {:,}  Queue: {:,}  Visited: {:,}\n\n'.format(*summary_output))
        else:
            output.write(*summary_output)
            output.write('\n\n')

        board_string = ''
        for y in range(self.NY):
            board_string += '    {}\n'.format(' '.join(display_board[x, y] for x in range(self.NX)))

        if not text_output:
            for letter in DISPLAY_TEXT[editor_mode]:
                board_string = board_string.replace(letter, DISPLAY_TEXT[editor_mode][letter])

        output.write(board_string + '\n')

        print(output.getvalue())


#-----------------------------------------------------------------------------------------
# Input file format:
#
# W wall
# _ empty space (converted to ' ' when file is read)
# P person
# p person on target
# B box
# b box on target
# T target
#-----------------------------------------------------------------------------------------
def read_level(opts):
    if opts.edit and opts.size is not None:
        person = (0, 0)
        boxes = None
        targets = None
        walls = None
        NX, NY = [int(x) for x in opts.size.split(',')]
        empty_board = {}
        raw_board = {}
        for y in range(NY):
            for x in range(NX):
                if x == 0 or x == NX - 1 or y == 0 or y == NY - 1:
                    empty_board[x, y] = 'W'
                    raw_board[x, y] = 'W'
                else:
                    empty_board[x, y] = ' '
                    raw_board[x, y] = ' '
    else:
        person = None
        boxes = []
        targets = []
        walls = []
        empty_board = {}
        raw_board = {}
        NX = 0
        NY = 0
        with open(opts.filename) as input_file:
            for y, line in enumerate(input_file):
                NY += 1
                converted_line = line.strip().replace(' ', ',').replace('_', ' ').split(',')
                for x, symbol in enumerate(converted_line):
                    raw_board[x, y] = symbol
                    empty_board[x, y] = EMPTY_BOARD_EQUIVALENT[symbol]
                    if NX == 0:
                        NX = len(converted_line)
                    if len(converted_line) != NX:
                        print('Check the input file. Line {} has length {}, not {}.'.format(y + 1, len(line), NX))
                        sys.exit()
                    if symbol in ('P', 'p'):
                        person = x, y
                    if symbol in ('B', 'b'):
                        boxes.append((x, y))
                    if symbol in ('T', 'p', 'b'):
                        targets.append((x, y))
                    if symbol == 'W':
                        walls.append((x, y))

        targets = frozenset(targets)
        walls = frozenset(walls)

        if not opts.edit:
            if person is None:
                print('There is no person in the input file.')
                sys.exit()

            if len(boxes) > len(targets):
                print('Check the input file. There are {} boxes, but only {} targets.'.format(len(boxes), len(targets)))
                sys.exit()
            elif len(targets) > len(boxes):
                print('Check the input file. There are {} targets, but only {} boxes.'.format(len(targets), len(boxes)))
                sys.exit()

    board = Board(NX, NY, raw_board, empty_board, targets, walls)
    start = State(person, boxes, '')

    return board, start


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def pause(interval):
    if interval > 0:
        time.sleep(interval)
    else:
        if input().lower().strip().startswith('q'):
            sys.exit()


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def move(a, b):
    return a[0] + b[0], a[1] + b[1]


#-----------------------------------------------------------------------------------------
# turn: 1 for clockwise, -1 for counter-clockwise.
#-----------------------------------------------------------------------------------------
def rotate(turn, a):
    return -turn * a[1], turn * a[0]


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def reverse(a):
    return -a[0], -a[1]


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def solution_filename(opts):
    directory = 'solutions'
    if opts.filename.endswith('.txt'):
        return os.path.join(directory, opts.filename.replace('.txt', '_solution.txt'))
    else:
        return os.path.join(directory, opts.filename + '_solution.txt')


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def print_history(history, line_length=0):
    i = 0
    if line_length == 0:
        print(history)
    else:
        while i < len(history):
            print(history[i:i+line_length])
            i += line_length


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def print_solution(opts, history):
    print()
    print_history(history)

    if not opts.no_file:
        output_filename = solution_filename(opts)
        with open(output_filename, 'w') as output_file:
            i = 0
            while i < len(history):
                output_file.write(history[i:i+80] + '\n')
                i += 80

        print()
        print('Solution file: {}'.format(output_filename))


#-----------------------------------------------------------------------------------------
# Print solution from file. This function does not check for errors in the solution.
#-----------------------------------------------------------------------------------------
def show_solution(start, board, opts):
    # This option can either be a file name or a solution string.
    if opts.user_solution:
        if os.path.exists(opts.user_solution):
            with open(opts.user_solution) as solution_file:
                solution = ''.join(line.strip() for line in solution_file)
        else:
            solution = opts.user_solution
    else:
        with open(solution_filename(opts)) as solution_file:
            solution = ''.join(line.strip() for line in solution_file)

    t = start
    number_pushes = 0

    board.print_current(t, opts.text_output, (0, 0))
    pause(opts.interval)
    for i, direction_name in enumerate(tuple(solution)):
        direction = DIRECTION[direction_name]
        new_position = move(t.person, direction)
        if new_position in t.boxes:
            across = move(new_position, direction)
            new_boxes = t.boxes[:]
            new_boxes.remove(new_position)
            new_boxes.append(across)
            t = State(new_position, new_boxes, t.history + direction_name)
            number_pushes += 1
        else:
            t = State(new_position, t.boxes, t.history + direction_name)
        board.print_current(t, opts.text_output, (i + 1, number_pushes), True, False)
        pause(opts.interval)


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def user_move(editor_mode=False):
    key = sys.stdin.read(1)

    # Command keys
    if  (not editor_mode and key in USER_KEYS) or (editor_mode and key in EDITOR_KEYS):
        return key

    # Arrow keys
    if ord(key) == 27:
        key2 = sys.stdin.read(1)
        if ord(key2) == 91:
            key3 = sys.stdin.read(1)
            #print(ord(key), ord(key2), ord(key3))
            #print( KEY_DIRECTION.get(ord(key3), None))
            return KEY_DIRECTION.get(ord(key3), None)


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def user_solve(start, board, opts):
    goal = len(board.targets)
    box_moved = []
    t = copy.deepcopy(start)
    number_of_moves = 0

    while True:
        board.print_current(t, opts.text_output, number_of_moves, True, False)
        direction = None
        while direction is None:
            direction = user_move()
        if direction in ('q', "'"):
            print_history(t.history)
            sys.exit()
        elif direction in ('r', 'p'):
            t = copy.deepcopy(start)
            number_of_moves = 0
        elif direction in ('u', 'g'):
            if not t.history:
                continue
            last_direction = DIRECTION[t.history[-1]]
            undo_direction = reverse(last_direction)
            new_position = move(t.person, undo_direction)
            across = move(t.person, last_direction)
            if box_moved.pop() and across in t.boxes:
                new_boxes = t.boxes[:]
                new_boxes.remove(across)
                new_boxes.append(t.person)
                t = State(new_position, new_boxes, t.history[:-1])
            else:
                t = State(new_position, t.boxes, t.history[:-1])
            number_of_moves -= 1
        else:
            new_position = move(t.person, direction)
            if board.legal_position(new_position):
                if new_position in t.boxes:
                    across = move(new_position, direction)
                    if board.legal_position(across) and across not in t.boxes:
                        new_boxes = t.boxes[:]
                        new_boxes.remove(new_position)
                        new_boxes.append(across)
                        if len(board.targets & set(new_boxes)) == goal:
                            # Solved!
                            final_state = State(new_position, new_boxes, t.history + DIRECTION_NAME[direction])
                            board.print_current(final_state, opts.text_output, number_of_moves + 1)
                            print('Solved!')
                            print()
                            print_history(final_state.history)
                            sys.exit()
                        elif opts.enforce and board.dead_end(direction, across, new_boxes):
                            continue
                        else:
                            t = State(new_position, new_boxes, t.history + DIRECTION_NAME[direction])
                            box_moved.append(True)
                            number_of_moves += 1
                else:
                    t = State(new_position, t.boxes, t.history + DIRECTION_NAME[direction])
                    box_moved.append(False)
                    number_of_moves += 1


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
def edit_level(start, board, opts):
    t = start
    t.person = (0, 0)
    while True:
        board.print_current(t, opts.text_output, None, True, True)
        direction = None
        while direction is None:
            direction = user_move(True)
        if direction in ('q', "'"):
            sys.exit()
        elif direction in ('s', 'o'):
            output_filename = get_user_input('Save file: ', opts)
            while not output_filename or os.path.exists(output_filename):
                output_filename = get_user_input('Save file: ', opts)
            with open(output_filename, 'w') as output_file:
                for y in range(board.NY):
                    for x in range(board.NX):
                        output_file.write(board.raw_board[x, y].replace(' ', '_'))
                        if x == board.NX - 1:
                            output_file.write('\n')
                        else:
                            output_file.write(' ')
            sys.exit()
        elif direction in ('p', 'l'):
            if board.raw_board[t.person] in ('T', 'b', 'p'):
                board.raw_board[t.person] = 'p'
            else:
                board.raw_board[t.person] = 'P'
        elif direction in ('b', 'x'):
            if board.raw_board[t.person] in ('T', 'b'):
                board.raw_board[t.person] = 'b'
            else:
                board.raw_board[t.person] = 'B'
                #number_boxes += 1
        elif direction in ('t', 'y'):
            if board.raw_board[t.person] in ('P', 'p'):
                board.raw_board[t.person] = 'p'
            elif board.raw_board[t.person] in ('B', 'b'):
                board.raw_board[t.person] = 'b'
            else:
                board.raw_board[t.person] = 'T'
        elif direction in ('w', ','):
            board.raw_board[t.person] = 'W'
        elif direction == ' ':
            board.raw_board[t.person] = ' '
        else:
            new_position = move(t.person, direction)
            if board.inbounds(new_position):
                t = State(new_position, None, None)


#-----------------------------------------------------------------------------------------
# Conduct a breadth first search (unless opts.random_search is True or opts.depth_first is True).
#-----------------------------------------------------------------------------------------
def search(start, board, opts):
    goal = len(board.targets)
    total_visited = 0
    explored = set()
    explored.add(start.signature())
    if opts.depth_first or opts.random_search:
        q = queue.LifoQueue()
    else:
        q = queue.Queue()
    #q.put(start)
    q.put(start.full_description(board))

    while not q.empty():
        #t = q.get()
        t = State(board, q.get())
        total_visited += 1
        if opts.show_board:
            board.print_current(t, opts.text_output, (datetime.now().strftime('%H:%M:%S'), len(t.history), q.qsize(), total_visited))
            #print('deq:', t)
            pause(opts.interval)
        elif total_visited % opts.print_interval == 0:
            if opts.level:
                board.print_current(t, opts.text_output, (datetime.now().strftime('%H:%M:%S'), len(t.history), q.qsize(), total_visited), False)
                print_history(t.history)
                print()
            else:
                print('Time: {}  Depth: {:,}  Queue: {:,}  Visited: {:,}'.format(datetime.now().strftime('%H:%M:%S'), len(t.history), q.qsize(), total_visited))
        directions = [U, R, D, L]
        if opts.random_search:
            random.shuffle(directions)
        for direction in directions:
            new_position = move(t.person, direction)
            if board.legal_position(new_position):
                new_state = None
                if new_position in t.boxes:
                    across = move(new_position, direction)
                    if board.legal_position(across) and across not in t.boxes:
                        new_boxes = t.boxes[:]
                        new_boxes.remove(new_position)
                        new_boxes.append(across)
                        if len(board.targets & set(new_boxes)) == goal:
                            # Solved!
                            final_state = State(new_position, new_boxes, t.history + DIRECTION_NAME[direction])
                            board.print_current(final_state, opts.text_output, (datetime.now().strftime('%H:%M:%S'), len(final_state.history), q.qsize(), total_visited + 1), opts.show_board)
                            print('Solved!')
                            print_solution(opts, final_state.history)
                            sys.exit()
                        elif board.dead_end(direction, across, new_boxes):
                            continue
                        else:
                            new_state = State(new_position, new_boxes, t.history + DIRECTION_NAME[direction])
                else:
                    new_state = State(new_position, t.boxes, t.history + DIRECTION_NAME[direction])
                if new_state is not None:
                    new_signature = new_state.signature()
                    if new_signature not in explored:
                        explored.add(new_signature)
                        #q.put(new_state)
                        q.put(new_state.full_description(board))

    print('No solution found. Check the input file.')


#-----------------------------------------------------------------------------------------
#
#-----------------------------------------------------------------------------------------
if __name__ == '__main__':
    parser = OptionParser()
    parser.add_option('-b', '--show-board', action='store_true', default=False, help='Show the board while solving')
    parser.add_option('-d', '--depth-first', action='store_true', default=False, help='Use depth first search instead of breadth first search')
    parser.add_option('-e', '--edit', action='store_true', default=False, help='Edit level (or create new file of size specified by "size")')
    parser.add_option('-f', '--filename', dest='filename', default='', help='File with level to solve', metavar='FILE')
    parser.add_option('-i', '--interval', type=float, default=0, help='Interval (seconds) per step while showing solution (if 0, keyboard input required to advance)')
    parser.add_option('-l', '--level', action='store_true', default=False, help='Show current level while solving')
    parser.add_option('-n', '--no-file', action='store_true', default=False, help='Do not create output solution file')
    parser.add_option('-p', '--print-interval', type=int, default=1, help='Print summary interval (in count of visited states)')
    parser.add_option('-r', '--random-search', action='store_true', default=False, help='Perform a random depth-first search')
    parser.add_option('-s', '--solution', action='store_true', default=False, help='Show solution')
    parser.add_option('-t', '--text-output', action='store_true', default=False, help='Print board in plain text')
    parser.add_option('-u', '--user', action='store_true', default=False, help='User solves the puzzle (with arrow keys and q(quit))')
    parser.add_option('-v', '--view', action='store_true', default=False, help='View level and quit')
    parser.add_option('-z', '--user-solution', default='', help='User supplied solution string or file name')
    parser.add_option('--enforce', action='store_true', default=False, help='Do not allow dead end moves in user mode')
    parser.add_option('--size', dest='size', help="'Size of new file to edit, in format 'NX,NY'")
    opts, _ = parser.parse_args()

    # TODO: Figure out why this works well with zsh, but not bash.
    if opts.user or opts.edit:
        tty.setcbreak(sys.stdin)

    board, start = read_level(opts)

    if opts.view:
        board.print_current(start, opts.text_output, 0)
    elif opts.user:
        user_solve(start, board, opts)
    elif opts.edit:
        edit_level(start, board, opts)
    elif opts.solution:
        show_solution(start, board, opts)
    else:
        search(start, board, opts)

    # Restore terminal settings.
    if opts.user or opts.edit:
        enable_echo()
