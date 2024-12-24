require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7260972 (f : El (fun num real)) (a : El num) (b : El num) (g : El (fun num real)) : Prf (⇒ (∀ (λ x : El num, (⇒ ((@IN num) x (… a b)) (= ((λ i : El num, (f i)) x) (g x))))) (= ((@sum num) (… a b) (λ i : El num, (f i))) ((@sum num) (… a b) g)));
