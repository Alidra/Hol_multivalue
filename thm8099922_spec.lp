require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8099922 [_143642 _143649] (r : El (fun _143649 (fun _143642 bool))) (s : El (fun _143649 (fun _143642 bool))) (x : El _143649) : Prf (= ((@COND _143642) ((@∃! _143642) ((@COND (fun _143642 bool)) (∃ (λ y : El _143642, (r x y))) (r x) (s x))) ((@ε _143642) ((@COND (fun _143642 bool)) (∃ (λ y : El _143642, (r x y))) (r x) (s x))) ((@ε _143642) (λ z : El _143642, F))) ((@COND _143642) (∃ (λ y : El _143642, (r x y))) ((@COND _143642) ((@∃! _143642) (r x)) ((@ε _143642) (r x)) ((@ε _143642) (λ z : El _143642, F))) ((@COND _143642) ((@∃! _143642) (s x)) ((@ε _143642) (s x)) ((@ε _143642) (λ z : El _143642, F)))));
