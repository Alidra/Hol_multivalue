require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (type180 a0)) (x1: El (type686 a0)) (x2: El (type686 a0)) ≔ (∀ (λ y0 : El (fun a0 bool), (⇒ ((@UNION_OF a0) x0 x1 y0) (x2 y0))));
symbol term1 a0 (x0: El (type180 a0)) (x1: El (type686 a0)) (x2: El (type686 a0)) ≔ (∀ (λ y0 : El (type686 a0), (⇒ (∧ (x0 y0) (∀ (λ y1 : El (fun a0 bool), (⇒ ((@IN (fun a0 bool)) y1 y0) (x1 y1))))) (x2 ((@UNIONS a0) y0)))));
