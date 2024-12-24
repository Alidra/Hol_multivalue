require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (type686 a0)) ≔ ((λ y0 : El (type686 a0), (∀ (λ y1 : El a0, (= ((@IN a0) y1 ((@INTERS a0) y0)) (∀ (λ y2 : El (fun a0 bool), (⇒ ((@IN (fun a0 bool)) y2 y0) ((@IN a0) y1 y2)))))))) x0);
symbol term1 a0 (x0: El (type686 a0)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 ((@INTERS a0) x0)) (∀ (λ y1 : El (fun a0 bool), (⇒ ((@IN (fun a0 bool)) y1 x0) ((@IN a0) y0 y1)))))));
symbol term2 a0 (x0: El (type686 a0)) (x1: El a0) ≔ ((λ y0 : El a0, (= ((@IN a0) y0 ((@INTERS a0) x0)) (∀ (λ y1 : El (fun a0 bool), (⇒ ((@IN (fun a0 bool)) y1 x0) ((@IN a0) y0 y1)))))) x1);
