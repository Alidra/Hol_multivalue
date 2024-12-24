require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7624600 [A B] : Prf (∀ (λ f : El (cart A B), (∀ (λ g : El (fun num A), (= (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex B) (@UNIV B)))) (= ((@﹩ A B) f i) (g i))))) (= ((@lambda A B) g) f))))));
