require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (fun a0 real)) ≔ ((λ y0 : El (fun a0 real), (∀ (λ y1 : El (fun a0 real), (∀ (λ y2 : El (fun a0 bool), (⇒ (∀ (λ y3 : El a0, (⇒ ((@IN a0) y3 y2) (= (y0 y3) (y1 y3))))) (= ((@sum a0) y2 (λ y3 : El a0, (y0 y3))) ((@sum a0) y2 y1)))))))) x0);
symbol term2 a0 (x0: El (fun a0 real)) (x1: El (fun a0 real)) ≔ ((λ y0 : El (fun a0 real), (∀ (λ y1 : El (fun a0 bool), (⇒ (∀ (λ y2 : El a0, (⇒ ((@IN a0) y2 y1) (= (x0 y2) (y0 y2))))) (= ((@sum a0) y1 (λ y2 : El a0, (x0 y2))) ((@sum a0) y1 y0)))))) x1);
symbol term4 a0 (x0: El (fun a0 real)) (x1: El (fun a0 real)) (x2: El (fun a0 bool)) ≔ ((λ y0 : El (fun a0 bool), (⇒ (∀ (λ y1 : El a0, (⇒ ((@IN a0) y1 y0) (= (x0 y1) (x1 y1))))) (= ((@sum a0) y0 (λ y1 : El a0, (x0 y1))) ((@sum a0) y0 x1)))) x2);
symbol term1 a0 (x0: El (fun a0 real)) ≔ (∀ (λ y0 : El (fun a0 real), (∀ (λ y1 : El (fun a0 bool), (⇒ (∀ (λ y2 : El a0, (⇒ ((@IN a0) y2 y1) (= (x0 y2) (y0 y2))))) (= ((@sum a0) y1 (λ y2 : El a0, (x0 y2))) ((@sum a0) y1 y0)))))));
symbol term3 a0 (x0: El (fun a0 real)) (x1: El (fun a0 real)) ≔ (∀ (λ y0 : El (fun a0 bool), (⇒ (∀ (λ y1 : El a0, (⇒ ((@IN a0) y1 y0) (= (x0 y1) (x1 y1))))) (= ((@sum a0) y0 (λ y1 : El a0, (x0 y1))) ((@sum a0) y0 x1)))));
