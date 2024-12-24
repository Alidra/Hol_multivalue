require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7622314 [A B] (g : El (fun num A)) : Prf (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex B) (@UNIV B)))) (= ((@﹩ A B) ((@lambda A B) g) i) (g i)))));
