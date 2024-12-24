require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (∀ (λ y2 : El num, (<= (dist ((@̦‚ num num) y0 y2)) (+ (dist ((@̦‚ num num) y0 y1)) (dist ((@̦‚ num num) y1 y2))))))))));
symbol term1 (x0: El num) ≔ (∀ (λ y0 : El num, (∀ (λ y1 : El num, (<= (dist ((@̦‚ num num) x0 y1)) (+ (dist ((@̦‚ num num) x0 y0)) (dist ((@̦‚ num num) y0 y1))))))));
symbol term0 (x0: El num) (x1: El num) ≔ (∀ (λ y0 : El num, (<= (dist ((@̦‚ num num) x0 y0)) (+ (dist ((@̦‚ num num) x0 x1)) (dist ((@̦‚ num num) x1 y0))))));
