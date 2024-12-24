require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8001314 [A N] : Prf (∀ (λ l : El (list A), (= ((@vector A N) l) ((@lambda A N) (λ i : El num, ((@EL A) (- i (NUMERAL (BIT1 _0))) l))))));
