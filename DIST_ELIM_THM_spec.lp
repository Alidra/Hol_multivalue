require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1246841 (y : El num) (x : El num) (P : El (fun num bool)) : Prf (= (P (dist ((@̦‚ num num) x y))) (∀ (λ d : El num, (∧ (⇒ (= x (+ y d)) (P d)) (⇒ (= y (+ x d)) (P d))))));
