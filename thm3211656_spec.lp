require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3211656 [A B] (y : El B) (s : El (fun A bool)) (f : El (fun A B)) : Prf ((λ f' : El (fun A B), (= ((@IN B) y ((@IMAGE A B) f' s)) (∃ (λ x : El A, (∧ (= y (f' x)) ((@IN A) x s)))))) f);
