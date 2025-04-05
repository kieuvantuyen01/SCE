#------------------------------LIBRARIES---------------------------------
# https://github.com/arminbiere/runlim (Runlim - to execute Cadical)
# https://github.com/arminbiere/kissat (Kissat)
### Kissat402 (4.0.2)
# https://pysathq.github.io/docs/html/api/solvers.html
### Glucose42 (4.2.1) or Glucose3
### Cadical195 (1.9.5)
from pysat.solvers import Solver, Glucose3, Glucose42
from prettytable import PrettyTable
from threading import Timer
# from datetime import datetime
import pandas
import os, sys

#------------------------------CONSTANTS---------------------------------
GLUCOSE3_NAME = "Glucose3"
GLUCOSE42_NAME = "Glucose42"
KISSAT402_NAME = "Kissat402"
CADICAL195_NAME = "Cadical195"

# GLUCOSE3_NAME, GLUCOSE42_NAME, KISSAT402_NAME, CADICAL195_NAME
ALL_SOLVER_NAME = [GLUCOSE3_NAME]
# [1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]
ALL_SOLVE_METHOD = [[1, 2, 3]]

time_budget = 900 # in seconds
num_groups: int  # number of groups
players_per_group: int  # players per group
num_weeks: int  # number of weeks
num_players: int  # players per group * number of groups
id_variable: int
all_clauses = []
id_counter = 0
num_long_clauses : int
num_short_clauses : int

sat_solver: Solver
solve_method: str
solver_name: str
enable_pythonsat: bool

filename = os.path.splitext(os.path.basename(__file__))[0]
online_path = ''
log_file = open(f'{online_path}logs/{filename}.log', 'a')

def plus_clause(clause):
    global num_long_clauses, num_short_clauses
    if enable_pythonsat: 
        # sat_solver.add_clause(clause)
        if (clause.__len__() < 3): num_short_clauses += 1
        else: num_long_clauses += 1
    else: 
        all_clauses.append(clause)

#--------------------------MAIN CONSTRAINTS-----------------------------
def generate_all_clauses(arr):
    global solve_method
    solve_method = f"{filename}_{arr[0]}{arr[1]}{arr[2]}"
    
    for i in arr:
        if i == 1:
            ensure_golfer_plays_at_least_once_per_week()
            assign_golfers_to_groups()
            ensure_golfer_plays_in_one_group_per_week()
        elif i == 2:
            ensure_unique_player_in_group_per_week()
            ensure_unique_position_for_player_in_group()
        elif i == 3:
            ensure_player_in_group_if_assigned_to_week()
            ensure_no_repeated_players_in_groups()
    
    generate_symmetry_breaking_clause1()
    generate_symmetry_breaking_clause2()
    generate_symmetry_breaking_clause3()

# (ALO) Every golfer plays at least once a week
# x_w_p_g (1)
def ensure_golfer_plays_at_least_once_per_week():
    """
    Ensures that each golfer plays at least once per week.
    """
    for player in range(1, num_players + 1):
        for week in range(1, num_weeks + 1):
            clause = []
            for position in range(1, players_per_group + 1):
                for group in range(1, num_groups + 1):
                    clause.append(get_variable(player, position, group, week))
            plus_clause(clause)


# (AMO) Each golfer plays at most once in each group each week
# x_w_p_g_p (2)
def assign_golfers_to_groups():
    """
    Assigns golfers to groups for each week and position using SAT solver.
    """
    for golfer in range(1, num_players + 1):
        for week in range(1, num_weeks + 1):
            for position in range(1, players_per_group + 1):
                for group in range(1, num_groups + 1):
                    for other_position in range(position + 1, players_per_group + 1):
                        clause = [-1 * get_variable(golfer, position, group, week),
                                    -1 * get_variable(golfer, other_position, group, week)]
                        plus_clause(clause)


# AMO_No golfer plays in more than one group in any week
# x_w_p_g_g_p (3)
def ensure_golfer_plays_in_one_group_per_week():
    """
    Ensures that each golfer plays in only one group per week.

    This function iterates over all players, weeks, positions, groups, and next groups,
    and adds a clause to the SAT solver to enforce that a player cannot be in two different groups in the same week.

    Parameters:
    None

    Returns:
    None
    """
    for player in range(1, num_players + 1):
        for week in range(1, num_weeks + 1):
            for position in range(1, players_per_group + 1):
                for group in range(1, num_groups + 1):
                    for next_group in range(group + 1, num_groups + 1):
                        for next_position in range(1, players_per_group + 1):
                            clause = [-1 * get_variable(player, position, group, week),
                                      -1 * get_variable(player, next_position, next_group, week)]
                            plus_clause(clause)

# (ALO) ensure each player appears only once in a group in a week
# w_g_p_x (4)
def ensure_unique_player_in_group_per_week():
    """
    Ensures that each player appears in only one group per week.

    This function iterates over each week, group, and position, and adds a clause
    to the SAT solver to ensure that each player appears in only one group per week.

    Args:
        None

    Returns:
        None
    """
    for week in range(1, num_weeks + 1):
        for group in range(1, num_groups + 1):
            for position in range(1, players_per_group + 1):
                clause = []
                for golfer in range(1, num_players + 1):
                    clause.append(get_variable(golfer, position, group, week))
                plus_clause(clause)

# (AMO) ensure no two players occupy the same position in the same group in the same week
# w_g_p_x_p (5)
def ensure_unique_position_for_player_in_group():
    """
    Ensures that each player has a unique position within their group for each week.
    """
    for week in range(1, num_weeks + 1):
        for group in range(1, num_groups + 1):
            for position in range(1, players_per_group + 1):
                for golfer in range(1, num_players + 1):
                    for other_golfer in range(golfer + 1, num_players + 1):
                        clause = [-1 * get_variable(golfer, position, group, week),
                                  -1 * get_variable(other_golfer, position, group, week)]
                        plus_clause(clause)


# This is a clause combining two sets of variables, ijkl and ikl (x_g_w_p) _6_
# ensure that if a player is in a group in a week, then they must be in one of the positions in that group, and vice versa
def ensure_player_in_group_if_assigned_to_week():
    """
    Ensures that each player is assigned to a group in each week.
    """
    for golfer in range(1, num_players + 1):
        for group in range(1, num_groups + 1):
            for week in range(1, num_weeks + 1):
                clause = [-1 * get_variable2(golfer, group, week)]
                for position in range(1, players_per_group + 1):
                    clause.append(get_variable(golfer, position, group, week))
                    clause2 = [get_variable2(golfer, group, week),
                               -1 * get_variable(golfer, position, group, week)]
                    plus_clause(clause2)
                plus_clause(clause)


# If two players m and n play in the same group k in week l, they cannot play together in any group together in future weeks
# w_g_x_x_g_w (7)
def ensure_no_repeated_players_in_groups():
    """
    Ensures that no players are repeated in the same group across different weeks and groups.
    """
    for week in range(1, num_weeks + 1):
        for group in range(1, num_groups + 1):
            for golfer1 in range(1, num_players + 1):
                for golfer2 in range(golfer1 + 1, num_players + 1):
                    for other_group in range(1, num_groups + 1):
                        for other_week in range(week + 1, num_weeks + 1):
                            clause = [-1 * get_variable2(golfer1, group, week),
                                      -1 * get_variable2(golfer2, group, week),
                                      -1 * get_variable2(golfer1, other_group, other_week),
                                      -1 * get_variable2(golfer2, other_group, other_week)]
                            plus_clause(clause)

#--------------------------SYMMETRY BREAKING-----------------------------
#(AMO) ensure no two players occupy the same position in the same group in the same week (x_p_g_w_x)
def generate_symmetry_breaking_clause1():
    for golfer1 in range(1, num_players + 1):
        for position1 in range(1, players_per_group):
            for group in range(1, num_groups + 1):
                for week in range(1, num_weeks + 1):
                    for golfer2 in range(1, golfer1 + 1):
                        clause = [-1 * get_variable(golfer1, position1, group, week),
                                  -1 * get_variable(golfer2, position1 + 1, group, week)]
                        plus_clause(clause)

# (AMO) A player cannot be in the first position of a group in a week if they are in the first position of the next group in the same week
# x_g_w_x
def generate_symmetry_breaking_clause2():
    for golfer1 in range(1, num_players + 1):
        for group in range(1, num_groups):
            for week in range(1, num_weeks + 1):
                for golfer2 in range(1, golfer1):
                    clause = [-1 * get_variable(golfer1, 1, group, week),
                              -1 * get_variable(golfer2, 1, group + 1, week)]
                    plus_clause(clause)

# (AMO) A player cannot be in the second position of the first group in a week if they are in the second position of the first group in the next week
def generate_symmetry_breaking_clause3():
    for golfer1 in range(1, num_players + 1):
        for week in range(1, num_weeks):
            for golfer2 in range(1, golfer1 + 1):
                clause = [-1 * get_variable(golfer1, 2, 1, week),
                          -1 * get_variable(golfer2, 2, 1, week + 1)]
                plus_clause(clause)

#-----------------------------OTHER PARTS--------------------------------
def get_variable(golfer, position, group, week):
    golfer -= 1
    position -= 1
    group -= 1
    week -= 1
    return golfer + (num_players * position) + (group * num_players * players_per_group) + (week * num_players * players_per_group * num_groups) + 1


def get_variable2(golfer, group, week):
    golfer -= 1
    group -= 1
    week -= 1
    return golfer + (num_players * group) + (week * num_players * num_groups) + 1 + (num_players * players_per_group * num_groups * num_weeks)


def resolve_variable(v):
    tmp = abs(v) - 1
    player = tmp % num_players + 1
    tmp //= num_players
    group = tmp % num_groups + 1
    tmp //= num_groups
    week = tmp + 1
    assert get_variable(player, group, week) == abs(v)
    return player, group, week

def write_to_csv(result_dict):
    # Append the result to a list
    csv_results = []
    csv_results.append(result_dict)

    output_path = online_path + 'reports'

    # Write the results to a CSV file
    if not os.path.exists(output_path): os.makedirs(output_path)

    df = pandas.DataFrame(csv_results)
    # current_date = datetime.now().strftime('%Y-%m-%d')
    # csv_file_path = f"{output_path}/results_{current_date}.csv"
    csv_file_path = f"{output_path}/{filename}.csv"

    # Check if the file already exists
    if os.path.exists(csv_file_path):
        df.to_csv(csv_file_path, mode='a', index=False, header=False)
    else:
        df.to_csv(csv_file_path, index=False, header=True)

    print(f"Result added to CSV file: {os.path.abspath(csv_file_path)}\n")

def check_legit(solution):
    def show_result(res):
        board = {}
        for week in range(1, num_weeks + 1):
            board[week] = {}
            for group in range(1, num_groups + 1):
                board[week][group] = []
        for row in res:
            board[row["week"]][row["group"]].append(row["player"])
        
        print_table = PrettyTable()
        field_names = ["Week"]
        for group in range(1, num_groups + 1):
            field_names.append("Group " + str(group))
        print_table.field_names = field_names
        for week in range(1, num_weeks + 1):
            row = [str(week)]
            for group in range(1, num_groups + 1):
                row.append(str(",".join(list(map(str, board[week][group])))))
            print_table.add_row(row)
        print(print_table)

    def show_result2(res):
        board = {}
        for week in range(1, num_weeks + 1):
            board[week] = {}
            for player in range(1, num_players + 1):
                board[week][player] = []
        for row in res:
            board[row["week"]][row["player"]] = row["group"]
        
        print_table = PrettyTable()
        field_names = ["W\\P"]
        for player in range(1, num_players + 1):
            field_names.append(str(player))
        print_table.field_names = field_names
        for week in range(1, num_weeks + 1):
            row = [str(week)]
            for player in range(1, num_players + 1):
                row.append(str(board[week][player]))
            print_table.add_row(row)
        print(print_table)

    def validate_result(res):
        table = {}
        for week in range(1, num_weeks + 1):
            table[week] = {}
            for group in range(1, num_groups + 1): table[week][group] = []

        for row in res:
            table[row["week"]][row["group"]].append(row["player"])

        # Check part 1
        has_played = [0 for i in range(num_players + 1)]
        for week in range(1, num_weeks + 1):
            for player in range(1, num_players + 1):
                has_played[player] = 0
            for group in range(1, num_groups + 1):
                for player in table[week][group]:
                    if has_played[player] == 1: return False
                    has_played[player] = 1

        # Check part 2
        for week in range(1, num_weeks + 1):
            for group in range(1, num_groups + 1):
                if len(table[week][group]) != players_per_group: return False

        # Check part 3
        play_together = [[0 for j in range(num_players + 1)] for i in range(num_players + 1)]
        for week in range(1, num_weeks + 1):
            for group in range(1, num_groups + 1):
                for id1 in range(0, players_per_group):
                    x = table[week][group][id1]
                    for id2 in range(id1 + 1, players_per_group):
                        y = table[week][group][id2]
                        if play_together[x][y] == 1:
                            return False
                        play_together[x][y] = 1
        return True

    result = []
    for v in solution:
        if abs(v) > num_players * num_groups * num_weeks: break
        if v > 0 and v <= num_players * num_groups * num_weeks:
            player, group, week = resolve_variable(v)
            result.append({"player": player, "group": group, "week": week})

    show_result(result)
    # show_result2(result)

    print("Checking validation of the solution...")
    if not validate_result(result):
        print("Invalid solution. TERMINATE right now.\n")
        return False
    print("Valid solution.\n")
    return True

def run_pythonsat(result_dict):
    # Store the number of variables and clauses before solving the problem
    num_vars = sat_solver.nof_vars()
    # num_clauses = sat_solver.nof_clauses()

    result_dict["Variables"] = num_vars
    # result_dict["Clauses"] = num_clauses
    result_dict["Long Clauses"] = num_long_clauses
    result_dict["Short Clauses"] = num_short_clauses
    # print("Variables: " + str(num_vars))
    # print("Clauses: " + str(num_clauses))

    print("Searching for a solution...")

    # def interrupt(s): s.interrupt()
    # timer = Timer(time_budget, interrupt, [sat_solver])
    # timer.start()
    # sat_status = sat_solver.solve_limited(expect_interrupt = True)

    # if sat_status is False:
    #     elapsed_time = float(format(sat_solver.time(), ".6f"))
    #     print(f"UNSAT. Time run: {elapsed_time}s.\n")
    #     result_dict["Result"] = "unsat"
    #     result_dict["Time"] = elapsed_time

    # else:
    #     solution = sat_solver.get_model()
    #     if solution is None:
    #         print(f"Time limit exceeded ({time_budget}s).\n")
    #         result_dict["Result"] = "timeout"
    #         result_dict["Time"] = time_budget
        
    #     else:
    #         elapsed_time = float(format(sat_solver.time(), ".6f"))
    #         print(f"A solution was found in {elapsed_time}s.")
    #         if not check_legit(solution): sys.exit(1)
    #         result_dict["Result"] = "sat"
    #         result_dict["Time"] = elapsed_time

    # timer.cancel()
    # sat_solver.delete()
    write_to_csv(result_dict)

def run_cadical(result_dict):
    # Store the number of variables and clauses before solving the problem
    num_vars = id_variable
    num_clauses = len(all_clauses)

    result_dict["Variables"] = num_vars
    result_dict["Clauses"] = num_clauses
    print("Variables: " + str(num_vars))
    print("Clauses: " + str(num_clauses))

    def write_to_input():
        # Write data to the file
        with open(input_file, 'w') as writer:
            # Write each clause to the file
            for clause in all_clauses:
                for literal in clause: writer.write(str(literal) + " ")
                writer.write("\n")
        
        all_clauses.clear()
        print(f"Input written to {os.path.abspath(input_file)}.\n")

    def handle_file():
        result_text = "timeout"
        time_run = time_budget
        solution = []

        with open(output_file, 'r') as file: lines = file.readlines()
        if lines[0] != "-1\n":
            time_run = float(lines[1])
            print(f"Time run: {time_run}s.")
            if lines[0] == "0\n": result_text = "unsat"
            else:
                result_text = "sat"
                solution = list(map(int, lines[2].split()))

        result_dict["Result"] = result_text
        result_dict["Time"] = time_run

        if result_text == "timeout": print(f"Time limit exceeded ({time_budget}s).\n")
        elif result_text == "sat":
            print(f"A solution was found in {time_run}s.")
            if not check_legit(solution): sys.exit(1)
        else: print(f"UNSAT. Time run: {time_run}s.\n")
    

    path = online_path + "all_cadical"
    input_file = os.path.join(path, "input.txt")
    output_file = os.path.join(path, "output.txt")

    write_to_input()

    print("Searching for a solution...")
    bashCommand = f"./all_cadical/runlim -r {time_budget + 10} -o all_cadical/report.txt python3 all_cadical/cadical.py"
    os.system(bashCommand)

    handle_file()
    write_to_csv(result_dict)

def run_kissat(problem_name, result_dict):
    # Store the number of variables and clauses before solving the problem
    num_vars = id_variable + (num_players * players_per_group * num_groups * num_weeks)
    num_clauses = len(all_clauses)

    result_dict["Variables"] = num_vars
    result_dict["Clauses"] = num_clauses
    print("Variables: " + str(num_vars))
    print("Clauses: " + str(num_clauses))

    def write_to_cnf():
        # Write data to the file
        with open(input_file, 'w') as writer:
            # Write a line of information about the number of variables and constraints
            writer.write(f"p cnf {num_vars} {num_clauses}\n")

            # Write each clause to the file
            for clause in all_clauses:
                for literal in clause: writer.write(str(literal) + " ")
                writer.write("0\n")
        
        all_clauses.clear()
        print(f"CNF written to {os.path.abspath(input_file)}.\n")

    def handle_file():
        result_text = "timeout"
        time_run = time_budget
        solution = []

        with open(output_file, 'r') as file: lines = file.readlines()
        for line in lines:
            if line.strip() == "s SATISFIABLE": result_text = "sat"
            elif line.strip() == "s UNSATISFIABLE": result_text = "unsat"
            elif result_text == "sat" and line.strip().startswith("v"):
                solution.extend(map(int, line.strip().split()[1:]))
            elif result_text != "timeout" and line.strip().startswith("c process-time:"):
                tmp = line.split()
                time_run = float(tmp[len(tmp) - 2])
                break

        result_dict["Result"] = result_text
        result_dict["Time"] = time_run

        if result_text == "timeout": print(f"Time limit exceeded ({time_budget}s).\n")
        elif result_text == "sat":
            print(f"A solution was found in {time_run}s.")
            solution.pop()  # Remove the last 0 from the solution
            # if not check_legit(solution): sys.exit(1)
        else: print(f"UNSAT. Time run: {time_run}s.\n")
    
    # Create the directory if it doesn't exist
    input_path = online_path + "all_kissat/input_cnf"
    if not os.path.exists(input_path): os.makedirs(input_path)

    # Create the directory if it doesn't exist
    output_path = online_path + "all_kissat/output_txt"
    if not os.path.exists(output_path): os.makedirs(output_path)

    input_file = os.path.join(input_path, problem_name + ".cnf")
    output_file = os.path.join(output_path, problem_name + ".txt")
    write_to_cnf()

    print("Searching for a solution...")
    bashCommand = f"ls {input_file} | xargs -n 1 ./all_kissat/kissat --time={time_budget} --relaxed > {output_file}"
    os.system(bashCommand)

    handle_file()
    write_to_csv(result_dict)

def solve_sat_problem():
    problem_name = f"{num_groups}-{players_per_group}-{num_weeks}"

    assert num_groups > 1 and players_per_group > 1
    global num_players, id_variable, sat_solver, id_counter, num_long_clauses, num_short_clauses
    num_players = players_per_group * num_groups
    
    global solve_method, solver_name
    global enable_pythonsat
    for solver_name in ALL_SOLVER_NAME:
        enable_pythonsat = (solver_name in [GLUCOSE3_NAME, GLUCOSE42_NAME])
        
        for arr in ALL_SOLVE_METHOD:
            id_variable = num_players * num_groups * num_weeks
            id_counter += 1
            num_long_clauses = 0
            num_short_clauses = 0

            print(
                f"Problem no. {id_counter}:\n" +
                f"- Number of groups: {num_groups}.\n" +
                f"- Players per group: {players_per_group}.\n" + 
                f"- Number of weeks: {num_weeks}.\n"
            )

            if solver_name == GLUCOSE3_NAME: sat_solver = Glucose3(use_timer=True)
            elif solver_name == GLUCOSE42_NAME: sat_solver = Glucose42(use_timer=True)
            generate_all_clauses(arr)

            result_dict = {
                "ID": id_counter,
                "Problem": problem_name,
                "Type": solve_method,
                "SAT Solver": solver_name,
                "Time": "",
                "Result": "",
                "Variables": 0,
                "Long Clauses": 0,
                "Short Clauses": 0,
                # "Clauses": 0
            }

            print(f"{solve_method} with {solver_name}:")
            if enable_pythonsat: run_pythonsat(result_dict)
            elif solver_name == CADICAL195_NAME: run_cadical(result_dict)
            elif solver_name == KISSAT402_NAME: run_kissat(problem_name, result_dict)

            print('-' * 120)

# Read input data from file data.txt, each line is a tuple of 3 integers:
# number of groups - number of players per group - number of weeks
def run_from_input_file():
    global num_groups, players_per_group, num_weeks
    with open(online_path + 'data.txt') as f:
        for line in f:
            num_groups, players_per_group, num_weeks = map(int, line.split())
            solve_sat_problem()

    log_file.close()

# Define a custom print function that writes to both console and log file
# def print(*args, **kwargs):
#     print(*args, **kwargs)
#     print(*args, file = log_file, **kwargs)
#     log_file.flush()

if __name__ == "__main__": run_from_input_file()