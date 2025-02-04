from typing import List, Set
import itertools
from pysat.solvers import Minisat22, Glucose3
from pysat.formula import CNF
import sys
import pandas as pd
from datetime import datetime
import os
from threading import Timer
import time

class SocialGolferProblem:
    def __init__(self, groups: int, players_per_group: int, weeks: int, solver_name: str = "glucose3", encoding_type: str = "sce_sbc_nsc"):
        self.g = groups
        self.p = players_per_group
        self.w = weeks
        self.q = groups * players_per_group
        self.solver_name = solver_name
        self.encoding_type = encoding_type
        self.time_limit = 600  # 600 seconds = 10 minutes
        
        # Khởi tạo CNF formula và các biến thống kê
        self.cnf = CNF()
        self.num_vars = 0
        self.num_clauses = 0
        self.encoding_time = 0
        self.solving_time = 0
        
        # Khởi tạo mapping biến
        self.var_mapping = {}
        self.reverse_mapping = {}
        self.next_var = 1
        
        # Tạo biến cho mỗi player trong mỗi group mỗi tuần
        for player in range(self.q):
            for week in range(self.w):
                for group in range(self.g):
                    self.var_mapping[(player, week, group)] = self.next_var
                    self.reverse_mapping[self.next_var] = (player, week, group)
                    self.next_var += 1
                    self.num_vars += 1

    def _add_clause(self, clause: List[int]):
        """Helper function để thêm mệnh đề và đếm"""
        self.cnf.append(clause)
        self.num_clauses += 1

    def encode(self):
        """Mã hóa bài toán với đo thời gian"""
        start_time = time.time()
        
        self._encode_players_per_group()
        self._encode_every_player_plays()
        self._encode_no_repeat_pairs()
        self._encode_first_week()
        self._encode_spread_first_players()
        
        self.encoding_time = time.time() - start_time
        return self.cnf

    def _encode_players_per_group(self):
        # Mỗi nhóm phải có đúng p người chơi
        for week in range(self.w):
            for group in range(self.g):
                players = []
                for player in range(self.q):
                    players.append(self.var_mapping[(player, week, group)])
                
                # Sử dụng AtMost và AtLeast để đảm bảo đúng p người
                self._add_cardinality_constraint(players, self.p)

    def _encode_every_player_plays(self):
        # Mỗi người chơi phải chơi mỗi tuần
        for player in range(self.q):
            for week in range(self.w):
                clause = []
                for group in range(self.g):
                    clause.append(self.var_mapping[(player, week, group)])
                self._add_clause(clause)

    def _encode_no_repeat_pairs(self):
        # Hai người chơi không thể chơi cùng nhóm quá 1 lần
        for p1, p2 in itertools.combinations(range(self.q), 2):
            for w1, w2 in itertools.combinations(range(self.w), 2):
                for g1 in range(self.g):
                    for g2 in range(self.g):
                        # if w1 > w2:
                            # Nếu p1, p2 ở cùng nhóm g1 tuần w1
                            # thì không thể ở cùng nhóm g2 tuần w2
                        self._add_clause([
                            -self.var_mapping[(p1, w1, g1)],
                            -self.var_mapping[(p2, w1, g1)],
                            -self.var_mapping[(p1, w2, g2)],
                            -self.var_mapping[(p2, w2, g2)]
                        ])

    def _encode_first_week(self):
        # SB1: Xếp tuần đầu tiên
        for i in range(self.q):
            group = i // self.p
            self._add_clause([self.var_mapping[(i, 0, group)]])

    def _encode_spread_first_players(self):
        # SB2: p người đầu tiên ở các nhóm khác nhau
        for week in range(1, self.w):
            for player in range(self.p):
                self._add_clause([self.var_mapping[(player, week, player)]])

    def _add_cardinality_constraint(self, literals: List[int], k: int):
        """
        Thêm ràng buộc cardinality sử dụng New Sequential Counter: đúng k biến trong literals phải True
        """
        # Thêm một biến giả -1 vào đầu danh sách để phù hợp với cài đặt NSC
        var = [-1] + literals
        n = len(var) - 1  # số biến thực sự (không tính biến giả)
        
        # Tạo mảng các biến phụ R[i][j]
        map_register = [[0 for j in range(k + 1)] for i in range(n)]
        for i in range(1, n):
            for j in range(1, min(i, k) + 1):
                map_register[i][j] = self.next_var
                self.next_var += 1

        # (1): If a bit is true, the first bit of the corresponding register is true
        for i in range(1, n):
            self._add_clause([-1 * var[i], map_register[i][1]])

        # (2): R[i - 1][j] = 1 => R[i][j] = 1
        for i in range(2, n):
            for j in range(1, min(i - 1, k) + 1):
                self._add_clause([-1 * map_register[i - 1][j], map_register[i][j]])

        # (3): If bit i is on and R[i - 1][j - 1] = 1 => R[i][j] = 1
        for i in range(2, n):
            for j in range(2, min(i, k) + 1):
                self._add_clause([-1 * var[i], -1 * map_register[i - 1][j - 1], map_register[i][j]])

        # (4): If bit i is off and R[i - 1][j] = 0 => R[i][j] = 0
        for i in range(2, n):
            for j in range(1, min(i - 1, k) + 1):
                self._add_clause([var[i], map_register[i - 1][j], -1 * map_register[i][j]])

        # (5): If bit i is off => R[i][i] = 0
        for i in range(1, k + 1):
            self._add_clause([var[i], -1 * map_register[i][i]])

        # (6): If R[i - 1][j - 1] = 0 => R[i][j] = 0
        for i in range(2, n):
            for j in range(2, min(i, k) + 1):
                self._add_clause([map_register[i - 1][j - 1], -1 * map_register[i][j]])

        # (7): (At least k) R[n - 1][k] = 1 or (n-th bit is true and R[n - 1][k - 1] = 1)
        self._add_clause([map_register[n - 1][k], var[n]])
        self._add_clause([map_register[n - 1][k], map_register[n - 1][k - 1]])

        # (8): (At most k) If i-th bit is true => R[i - 1][k] = 0
        for i in range(k + 1, n + 1):
            self._add_clause([-1 * var[i], -1 * map_register[i - 1][k]])

    def validate_solution(self, schedule: List[List[Set[int]]]) -> bool:
        """
        Kiểm tra tính hợp lệ của lời giải theo các ràng buộc của SCE với SB1 và SB2
        Args:
            schedule: Lịch chơi golf [week][group] = set of players
        Returns:
            bool: True nếu lời giải hợp lệ, False nếu không
        """
        try:
            # Constraint (1): p players per group every weeks
            for week in range(self.w):
                for group in range(self.g):
                    if len(schedule[week][group]) != self.p:
                        print(f"ERROR: Week {week+1}, group {group} must have exactly {self.p} players")
                        return False

            # Constraint (2): Every golfer plays every weeks
            for week in range(self.w):
                players_this_week = set()
                for group in range(self.g):
                    players_this_week.update(schedule[week][group])
                if players_this_week != set(range(self.q)):
                    print(f"ERROR: Week {week+1}, all players must play")
                    return False

            # Constraint (4): Two players cannot play twice together
            player_pairs = set()  # (player1, player2) for player1 < player2
            for week in range(self.w):
                for group in range(self.g):
                    players = sorted(list(schedule[week][group]))
                    for i in range(len(players)):
                        for j in range(i + 1, len(players)):
                            pair = (players[i], players[j])
                            if pair in player_pairs:
                                print(f"ERROR: Players {pair} meet more than once")
                                return False
                            player_pairs.add(pair)

            # Constraint (6): First week assignment (SB1)
            for player in range(self.q):
                expected_group = player // self.p
                if player not in schedule[0][expected_group]:
                    print(f"ERROR: Week 1, player {player} must be in group {expected_group}")
                    return False

            # Constraint (7): First p players spread in different groups (SB2)
            for week in range(1, self.w):
                for player in range(self.p):
                    if player not in schedule[week][player]:
                        print(f"ERROR: Week {week+1}, player {player} must be in group {player}")
                        return False

            return True

        except Exception as e:
            print(f"ERROR: Exception during validation: {str(e)}")
            return False

    def solve(self):
        """Giải bài toán với timeout"""
        # Chọn solver
        if self.solver_name == "glucose3":
            solver = Glucose3(use_timer=True)
        else:
            solver = Minisat22()
        
        solver.append_formula(self.cnf)
        
        # Tạo timer để handle timeout
        timer = Timer(self.time_limit - self.encoding_time, lambda s: s.interrupt(), [solver])
        timer.start()
        
        try:
            start_time = time.time()
            if solver.solve():
                self.solving_time = time.time() - start_time
                model = solver.get_model()
                solution = self._decode_solution(model)
                
                # Validate solution
                if not self.validate_solution(solution):
                    print("Invalid solution found. Terminating...")
                    sys.exit(1)
                
                return "SAT", solution
            else:
                self.solving_time = time.time() - start_time
                return "UNSAT", None
                
        except Exception as e:
            self.solving_time = self.time_limit - self.encoding_time
            return "timeout", None
            
        finally:
            timer.cancel()
            solver.delete()

    def get_statistics(self) -> dict:
        """Trả về thống kê của lần chạy"""
        total_time = self.encoding_time + self.solving_time
        
        return {
            "Problem": f"{self.g}-{self.p}-{self.w}",
            "Type": self.encoding_type,
            "Solver": self.solver_name,
            "Variables": self.num_vars,
            "Clauses": self.num_clauses,
            "Time": total_time if total_time < self.time_limit else self.time_limit,
            "Result": "timeout" if total_time >= self.time_limit else "running"  # sẽ được cập nhật sau
        }

    def _decode_solution(self, model: List[int]) -> List[List[Set[int]]]:
        """
        Chuyển đổi lời giải SAT thành lịch chơi golf
        """
        schedule = [[set() for _ in range(self.g)] for _ in range(self.w)]
        
        for var in model:
            if var > 0 and var in self.reverse_mapping:  # Chỉ xử lý các biến chính
                player, week, group = self.reverse_mapping[var]
                schedule[week][group].add(player)
                    
        return schedule

def write_results_to_csv(results: List[dict], filename: str = "results.csv"):
    """Ghi kết quả ra file CSV"""
    df = pd.DataFrame(results)
    
    # Tạo thư mục output nếu chưa tồn tại
    output_dir = "output"
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Thêm ngày vào tên file
    date_str = datetime.now().strftime('%Y-%m-%d')
    filepath = os.path.join(output_dir, f"{filename}_{date_str}.csv")
    
    # Ghi file
    if os.path.exists(filepath):
        # Nếu file đã tồn tại, append không ghi header
        df.to_csv(filepath, mode='a', header=False, index=False)
    else:
        # Nếu file chưa tồn tại, tạo mới với header
        df.to_csv(filepath, index=False)
    
    print(f"Results written to {filepath}")

def run_from_input_file(input_file: str = "data.txt"):
    """
    Đọc và chạy các test case từ file input
    File format: mỗi dòng chứa 3 số nguyên: groups players_per_group weeks
    """
    results = []
    solvers = ["glucose3"]  # Danh sách các solver cần test
    encoding_types = ["sce_sbc_nsc"]  # Danh sách các encoding cần test
    
    try:
        with open(input_file, 'r') as f:
            for line in f:
                # Đọc thông số từ file
                groups, players_per_group, weeks = map(int, line.strip().split())
                print(f"\nTesting instance: {groups}-{players_per_group}-{weeks}")
                
                # Chạy với mỗi cấu hình solver và encoding
                for solver_name in solvers:
                    for encoding_type in encoding_types:
                        print(f"\nRunning with solver={solver_name}, encoding={encoding_type}")
                        
                        # Khởi tạo problem
                        problem = SocialGolferProblem(
                            groups=groups,
                            players_per_group=players_per_group,
                            weeks=weeks,
                            solver_name=solver_name,
                            encoding_type=encoding_type
                        )
                        
                        # Mã hóa bài toán
                        problem.encode()
                        
                        # Giải và lấy kết quả
                        result, solution = problem.solve()
                        
                        # Lấy thống kê và cập nhật kết quả
                        stats = problem.get_statistics()
                        stats["Result"] = result
                        results.append(stats)
                        
                        # In kết quả nếu tìm được
                        if solution:
                            print("\nFound solution:")
                            for week in range(len(solution)):
                                print(f"Week {week + 1}:")
                                for group in range(len(solution[week])):
                                    print(f"  Group {group + 1}: {solution[week][group]}")
                        
                        # Ghi kết quả ra file sau mỗi lần chạy
                        write_results_to_csv(results)
                        
    except FileNotFoundError:
        print(f"Error: Input file '{input_file}' not found")
        sys.exit(1)
    except Exception as e:
        print(f"Error while reading input file: {str(e)}")
        sys.exit(1)

def main():
    # Đường dẫn đến file input
    input_file = "data.txt"
    
    # Chạy các test case từ file
    run_from_input_file(input_file)

if __name__ == "__main__":
    main()
    
    