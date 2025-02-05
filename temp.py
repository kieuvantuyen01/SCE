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
            self.next_var = max_var + 1
        
        # Thêm tất cả các mệnh đề vào formula chính
        for clause in cnf.clauses:
            self._add_clause(clause)