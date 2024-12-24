require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem150645 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ n : El num, (⇒ (<= x y) (<= (EXP x n) (EXP y n)))))))));
