require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term3 (x0: El (fun num real)) ≔ (λ y0 : El num, (x0 y0));
symbol term1 (x0: El (fun num real)) (x1: El (fun num bool)) (x2: El (fun num real)) ≔ (⇒ (∀ (λ y0 : El num, (⇒ ((@IN num) y0 x1) (= (x0 y0) (x2 y0))))) (= ((@sum num) x1 x0) ((@sum num) x1 x2)));
symbol term0 a0 (x0: El (fun a0 real)) (x1: El (fun a0 bool)) (x2: El (fun a0 real)) ≔ (⇒ (∀ (λ y0 : El a0, (⇒ ((@IN a0) y0 x1) (= (x0 y0) (x2 y0))))) (= ((@sum a0) x1 x0) ((@sum a0) x1 x2)));
symbol term2 (x0: El (fun num real)) (x1: El num) (x2: El num) (x3: El (fun num real)) ≔ (⇒ (∀ (λ y0 : El num, (⇒ ((@IN num) y0 (… x1 x2)) (= ((λ y1 : El num, (x0 y1)) y0) (x3 y0))))) (= ((@sum num) (… x1 x2) (λ y0 : El num, (x0 y0))) ((@sum num) (… x1 x2) x3)));
