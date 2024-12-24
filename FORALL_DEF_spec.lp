require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem52 [A] : Prf (= (@∀ A) (λ P : El (fun A bool), (= P (λ x : El A, T))));
