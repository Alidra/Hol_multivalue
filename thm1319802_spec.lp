require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1319802 : Prf (∀ (λ x : El hreal, (∀ (λ y : El hreal, (⇒ (hreal_le x y) (∃ (λ d : El hreal, (= y (hreal_add x d)))))))));
