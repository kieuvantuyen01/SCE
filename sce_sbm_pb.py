from typing import List, Set
import itertools
from pysat.solvers import Minisat22, Glucose3
from pysat.formula import CNF
from pysat.pb import *
import sys
import pandas as pd
from datetime import datetime
import os
from threading import Timer
import time

class SocialGolferSBM:
    def __init__(self, groups: int, players_per_group: int, weeks: int, solver_name: str = "glucose3", encoding_type: str = "sce_sbm_pb"):
        self.g = groups  # số nhóm mỗi tuần
        self.p = players_per_group  # số người chơi mỗi nhóm  
        self.w = weeks  # số tuần
        self.q = groups * players_per_group  # tổng số người chơi
        self.solver_name = solver_name
        self.encoding_type = encoding_type
        self.time_limit = 600  # 600 seconds = 10 minutes
        
        # Khởi tạo solver ngay từ đầu
        if self.solver_name == "glucose3":
            self.solver = Glucose3()
        else:
            self.solver = Minisat22()
        
        # Khởi tạo các biến thống kê
        self.num_vars = 0
        self.num_clauses = 0
        self.encoding_time = 0
        self.solving_time = 0
        
        # Tạo biến cho mỗi player trong mỗi group mỗi tuần
        # Với SBM, chúng ta sẽ sử dụng G'[i,j] thay vì G[i,j]
        self.var_mapping = {}
        self.reverse_mapping = {}
        self.next_var = 1
        
        # Tạo biến cho tuần đầu tiên - G[i,j] = G'[i,j]
        for player in range(self.q):
            group = player // self.p
            for g in range(self.g):
                if g == group:
                    self.var_mapping[(0, g, player)] = self.next_var
                    self.reverse_mapping[self.next_var] = (0, g, player)
                    self.next_var += 1
                    self.num_vars += 1
        
        # Tạo biến cho các tuần còn lại
        for week in range(1, self.w):
            for group in range(self.g):
                # Với p người đầu tiên, họ được cố định vào các nhóm
                # Nếu j ≤ p: G[i,j] = G'[i,j] ∪ {pj}
                if group < self.p:
                    players = set(range(self.p, self.q))  # Chỉ cần p-1 người chơi khác
                # Ngược lại: G[i,j] = G'[i,j]
                else:
                    players = set(range(self.q))
                
                for player in players:
                    self.var_mapping[(week, group, player)] = self.next_var
                    self.reverse_mapping[self.next_var] = (week, group, player)
                    self.next_var += 1
                    self.num_vars += 1

    def _add_clause(self, clause: List[int]):
        """Helper function để thêm mệnh đề trực tiếp vào solver"""
        self.solver.add_clause(clause)
        self.num_clauses += 1

    def encode(self):
        """Mã hóa bài toán với đo thời gian"""
        start_time = time.time()
        
        # Thêm từng ràng buộc, mỗi ràng buộc sẽ thêm các mệnh đề trực tiếp vào solver
        self._encode_first_week()
        self._encode_players_per_group()
        self._encode_every_player_plays()
        self._encode_no_repeat_pairs()
        
        self.encoding_time = time.time() - start_time

    def _encode_first_week(self):
        # Constraint (8): Cố định tuần đầu tiên
        for i in range(self.q):
            group = i // self.p
            self._add_clause([self.var_mapping[(0, group, i)]])

    def _encode_players_per_group(self):
        # Tuần đầu tiên đã được cố định bởi constraint (8)
        
        # Constraint (10): Các nhóm có index <= p trong các tuần > 1 có p-1 người chơi
        # (vì đã có 1 người cố định)
        for week in range(1, self.w):
            for group in range(self.p):
                players = [self.var_mapping[(week, group, player)] 
                          for player in range(self.p, self.q)]
                self._add_cardinality_constraint(players, self.p-1)
        
        # Constraint (11): Các nhóm còn lại có p người chơi
        for week in range(1, self.w):
            for group in range(self.p, self.g):
                players = [self.var_mapping[(week, group, player)] 
                          for player in range(self.q)]
                self._add_cardinality_constraint(players, self.p)

    def _encode_every_player_plays(self):
        # Constraint (12): Mỗi người chơi (trừ p người đầu) phải chơi mỗi tuần
        for week in range(1, self.w):
            for player in range(self.p, self.q):
                clause = []
                for group in range(self.g):
                    if (week, group, player) in self.var_mapping:
                        clause.append(self.var_mapping[(week, group, player)])
                self._add_clause(clause)
        
    def _encode_no_repeat_pairs(self):
        # Constraint (13): Giữa các nhóm có index ≤ p
        for w1, w2 in itertools.combinations(range(1, self.w), 2):
            for g in range(self.p):
                for player in range(self.p, self.q):
                    if (w1, g, player) in self.var_mapping and (w2, g, player) in self.var_mapping:
                        self._add_clause([-self.var_mapping[(w1, g, player)], 
                                       -self.var_mapping[(w2, g, player)]])

        # Constraints (14)-(16): Không có cặp người chơi nào gặp nhau 2 lần
        for w1, w2 in itertools.combinations(range(self.w), 2):
            for g1 in range(self.g):
                for g2 in range(self.g):
                    for p1, p2 in itertools.combinations(range(self.q), 2):
                        if (w1, g1, p1) in self.var_mapping and \
                           (w1, g1, p2) in self.var_mapping and \
                           (w2, g2, p1) in self.var_mapping and \
                           (w2, g2, p2) in self.var_mapping:
                            self._add_clause([-self.var_mapping[(w1, g1, p1)],
                                           -self.var_mapping[(w1, g1, p2)],
                                           -self.var_mapping[(w2, g2, p1)],
                                           -self.var_mapping[(w2, g2, p2)]])

    # def _encode_no_repeat_pairs(self):
    #     """Mã hoá ràng buộc không có cặp người chơi nào gặp nhau 2 lần"""
    #     if self.w == 1: return
        
    #     # Biến phụ tmp[w] = 1 nếu player i và j gặp nhau ở tuần w
    #     tmp = [0 for _ in range(self.w + 1)]  # Thêm 1 phần tử để index từ 1
        
    #     def at_most_one_meeting(p1: int, p2: int):
    #         """Đảm bảo 2 người chơi p1, p2 gặp nhau nhiều nhất 1 lần"""
    #         # Tạo biến phụ cho mỗi tuần
    #         for w in range(1, self.w):
    #             self.next_var += 1
    #             self.num_vars += 1  # Đếm biến phụ
    #             tmp[w] = self.next_var
    #         self.next_var += 1
    #         self.num_vars += 1
    #         tmp[self.w] = self.next_var
            
    #         # Mã hoá: tmp[w] = 1 nếu p1, p2 gặp nhau ở tuần w
    #         for w in range(self.w):
    #             for g in range(self.g):
    #                 if (w, g, p1) in self.var_mapping and (w, g, p2) in self.var_mapping:
    #                     # Nếu cả 2 cùng trong nhóm g tuần w -> tmp[w+1] = 1
    #                     self._add_clause([-self.var_mapping[(w, g, p1)], 
    #                                 -self.var_mapping[(w, g, p2)], 
    #                                 tmp[w+1]])
    #                     # Nếu 1 người trong nhóm g tuần w -> tmp[w+1] = 0
    #                     self._add_clause([-self.var_mapping[(w, g, p1)],
    #                                 self.var_mapping[(w, g, p2)],
    #                                 -tmp[w+1]])
            
    #         # Mã hoá: tmp[w1] và tmp[w2] không thể cùng = 1
    #         for w1 in range(1, self.w + 1):
    #             for w2 in range(w1 + 1, self.w + 1):
    #                 self._add_clause([-tmp[w1], -tmp[w2]])
        
    #     # Áp dụng cho mọi cặp người chơi
    #     for p1 in range(self.q):
    #         for p2 in range(p1 + 1, self.q):
    #             at_most_one_meeting(p1, p2)

    def _add_cardinality_constraint(self, literals: List[int], k: int):
        """
        Thêm ràng buộc cardinality sử dụng PBLib: đúng k biến trong literals phải True
        """
        # Sử dụng PBLib để tạo mệnh đề CNF cho ràng buộc exactly-k
        # top_id là ID lớn nhất hiện tại để tránh xung đột biến phụ
        cnf = PBEnc.equals(lits=literals, bound=k, encoding=EncType.seqcounter, top_id=self.next_var)
        
        # Cập nhật next_var để tránh xung đột với các biến phụ được tạo bởi PBLib
        if len(cnf.clauses) > 0:
            max_var = max(abs(lit) for clause in cnf.clauses for lit in clause)
            self.num_vars += max_var - self.num_vars + 1
            self.next_var = max_var + 1
        
        # Thêm tất cả các mệnh đề vào formula chính
        for clause in cnf.clauses:
            self._add_clause(clause)

    def validate_solution(self, schedule: List[List[Set[int]]]) -> bool:
        """
        Kiểm tra tính hợp lệ của lời giải theo các ràng buộc của SCE^SBM
        Args:
            schedule: Lịch chơi golf [week][group] = set of players
        Returns:
            bool: True nếu lời giải hợp lệ, False nếu không
        """
        try:
            # Constraint (8): Kiểm tra tuần đầu tiên đã được cố định đúng
            for player in range(self.q):
                group = player // self.p
                if player not in schedule[0][group]:
                    print(f"ERROR: Week 1, player {player} must be in group {group}")
                    return False

            # Constraints (9)-(11): Kiểm tra số người chơi trong mỗi nhóm
            for week in range(self.w):
                for group in range(self.g):
                    if week == 0:
                        # Tuần đầu: mỗi nhóm có đúng p người
                        if len(schedule[week][group]) != self.p:
                            print(f"ERROR: Week 1, group {group} must have exactly {self.p} players")
                            return False
                    else:
                        # Các tuần sau:
                        if group < self.p:
                            # Nhóm ≤ p: có p người (p-1 người + 1 người cố định)
                            if len(schedule[week][group]) != self.p:
                                print(f"ERROR: Week {week+1}, group {group} must have exactly {self.p} players")
                                return False
                            # Kiểm tra người cố định
                            if group not in schedule[week][group]:
                                print(f"ERROR: Week {week+1}, player {group} must be fixed in group {group}")
                                return False
                        else:
                            # Nhóm > p: có p người
                            if len(schedule[week][group]) != self.p:
                                print(f"ERROR: Week {week+1}, group {group} must have exactly {self.p} players")
                                return False

            # Constraint (12): Mỗi người chơi phải chơi mỗi tuần (trừ p người đầu với tuần > 1)
            for week in range(self.w):
                players_this_week = set()
                for group in range(self.g):
                    players_this_week.update(schedule[week][group])
                
                if week == 0:
                    # Tuần đầu: tất cả người chơi phải tham gia
                    if players_this_week != set(range(self.q)):
                        print(f"ERROR: Week 1, all players must play")
                        return False
                else:
                    # Các tuần sau: tất cả người chơi từ p trở đi phải tham gia
                    if not players_this_week.issuperset(set(range(self.p, self.q))):
                        print(f"ERROR: Week {week+1}, all players from {self.p} to {self.q-1} must play")
                        return False

            # Constraints (13)-(16): Không có cặp người chơi nào gặp nhau 2 lần
            player_pairs = set()  # (player1, player2, week) for player1 < player2
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

            return True

        except Exception as e:
            print(f"ERROR: Exception during validation: {str(e)}")
            return False

    def solve(self):
        """Giải bài toán với timeout"""
        # Tạo timer để handle timeout
        timer = Timer(self.time_limit - self.encoding_time, lambda s: s.interrupt(), [self.solver])
        timer.start()
        
        try:
            start_time = time.time()
            if self.solver.solve():
                self.solving_time = time.time() - start_time
                model = self.solver.get_model()
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
        Với SB2: G[i,j] = G'[i,j] ∪ {pj} nếu j ≤ p và tuần > 1
        """
        schedule = [[set() for _ in range(self.g)] for _ in range(self.w)]
        
        for var in model:
            if var > 0 and var in self.reverse_mapping:
                week, group, player = self.reverse_mapping[var]
                schedule[week][group].add(player)
                # Thêm người chơi cố định cho các nhóm có index <= p từ tuần thứ 2
                if week > 0 and group < self.p:
                    schedule[week][group].add(group)
                
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
    encoding_types = ["sce_sbm_pb"]  # Danh sách các encoding cần test
    
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
                        problem = SocialGolferSBM(
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
                        # if solution:
                        #     print("\nFound solution:")
                        #     for week in range(len(solution)):
                        #         print(f"Week {week + 1}:")
                        #         for group in range(len(solution[week])):
                        #             print(f"  Group {group + 1}: {solution[week][group]}")
                        
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