require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7055650 : Prf (∀ (λ f : El (fun num num), (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (= (MOD ((@nsum num) (… a b) f) n) (MOD ((@nsum num) (… a b) (λ i : El num, (MOD (f i) n))) n))))))))));
