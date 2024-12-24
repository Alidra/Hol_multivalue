require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7261462 (f : El (fun num real)) (a : El num) (b : El num) (g : El (fun num real)) : Prf (= ((λ b' : El num, (⇒ (∀ (λ i : El num, (⇒ (∧ (<= a i) (<= i b')) (= (f i) (g i))))) (= ((@sum num) (… a b') (λ i : El num, (f i))) ((@sum num) (… a b') g)))) b) (⇒ (∀ (λ i : El num, (⇒ (∧ (<= a i) (<= i b)) (= (f i) (g i))))) (= ((@sum num) (… a b) (λ i : El num, (f i))) ((@sum num) (… a b) g))));
