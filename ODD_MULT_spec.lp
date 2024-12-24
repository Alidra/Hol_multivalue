require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem128115 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= (ODD (* m n)) (∧ (ODD m) (ODD n)))))));
