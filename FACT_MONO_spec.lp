require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem146572 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (<= (FACT m) (FACT n)))))));
