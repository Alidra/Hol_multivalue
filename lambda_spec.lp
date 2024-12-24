require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7618353 [A B] : Prf (∀ (λ g : El (fun num A), (= ((@lambda A B) g) ((@ε (cart A B)) (λ f : El (cart A B), (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex B) (@UNIV B)))) (= ((@﹩ A B) f i) (g i))))))))));
