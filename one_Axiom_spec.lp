require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16237 [A] : Prf (∀ (λ e : El A, ((@∃! (fun 1 A)) (λ fn : El (fun 1 A), (= (fn one) e)))));
