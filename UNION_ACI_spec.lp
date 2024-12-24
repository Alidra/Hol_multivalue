require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3303082 [_86426] (r : El (fun _86426 bool)) (p : El (fun _86426 bool)) (q : El (fun _86426 bool)) : Prf (∧ (= ((@UNION _86426) p q) ((@UNION _86426) q p)) (∧ (= ((@UNION _86426) ((@UNION _86426) p q) r) ((@UNION _86426) p ((@UNION _86426) q r))) (∧ (= ((@UNION _86426) p ((@UNION _86426) q r)) ((@UNION _86426) q ((@UNION _86426) p r))) (∧ (= ((@UNION _86426) p p) p) (= ((@UNION _86426) p ((@UNION _86426) p q)) ((@UNION _86426) p q))))));
