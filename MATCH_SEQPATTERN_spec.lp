require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8099923 [_143642 _143649] (r : El (fun _143649 (fun _143642 bool))) (x : El _143649) (s : El (fun _143649 (fun _143642 bool))) : Prf (= ((@_MATCH _143649 _143642) x ((@_SEQPATTERN _143642 _143649) r s)) ((@COND _143642) (∃ (λ y : El _143642, (r x y))) ((@_MATCH _143649 _143642) x r) ((@_MATCH _143649 _143642) x s)));
