require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem280136 : Prf (∀ (λ P : El (fun num bool), (∀ (λ n : El num, (⇒ (P n) (<= (minimal P) n))))));
