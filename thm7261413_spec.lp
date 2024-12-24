require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7261413 (f : El (fun num real)) : Prf (∀ (λ g : El (fun num real), (∀ (λ a : El num, (∀ (λ b : El num, (⇒ (∀ (λ i : El num, (⇒ (∧ (<= a i) (<= i b)) (= (f i) (g i))))) (= ((@sum num) (… a b) (λ i : El num, (f i))) ((@sum num) (… a b) g)))))))));
