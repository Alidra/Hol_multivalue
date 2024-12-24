require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3297116 [_86360] (r : El (fun _86360 bool)) (p : El (fun _86360 bool)) (q : El (fun _86360 bool)) : Prf (∧ (= ((@INTER _86360) p q) ((@INTER _86360) q p)) (∧ (= ((@INTER _86360) ((@INTER _86360) p q) r) ((@INTER _86360) p ((@INTER _86360) q r))) (∧ (= ((@INTER _86360) p ((@INTER _86360) q r)) ((@INTER _86360) q ((@INTER _86360) p r))) (∧ (= ((@INTER _86360) p p) p) (= ((@INTER _86360) p ((@INTER _86360) p q)) ((@INTER _86360) p q))))));
