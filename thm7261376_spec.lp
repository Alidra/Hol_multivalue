require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7261376 (a : El num) (b : El num) (f : El (fun num real)) (g : El (fun num real)) (h1 : Prf (∀ (λ i : El num, (⇒ (∧ (<= a i) (<= i b)) (= (f i) (g i)))))) : Prf (= ((@sum num) (… a b) (λ i : El num, (f i))) ((@sum num) (… a b) g));
