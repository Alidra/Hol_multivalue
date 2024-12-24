require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211684 [A] (s : El (fun A bool)) (x : El A) (y : El A) : Prf (= ((λ y' : El A, (= ((@IN A) x ((@DELETE A) s y')) (∧ ((@IN A) x s) (¬ (= x y'))))) y) (= ((@IN A) x ((@DELETE A) s y)) (∧ ((@IN A) x s) (¬ (= x y)))));
