require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El (fun num num)) ≔ (∃ (λ y0 : El num, (∀ (λ y1 : El num, (∀ (λ y2 : El num, (<= (dist ((@̦‚ num num) (* y1 (x0 y2)) (* y2 (x0 y1)))) (* y0 (+ y1 y2)))))))));
symbol term3 ≔ (∀ (λ y0 : El (fun num num), (= (is_nadd y0) (∃ (λ y1 : El num, (∀ (λ y2 : El num, (∀ (λ y3 : El num, (<= (dist ((@̦‚ num num) (* y2 (y0 y3)) (* y3 (y0 y2)))) (* y1 (+ y2 y3))))))))))));
symbol term4 (x0: El (fun num num)) ≔ ((λ y0 : El (fun num num), (= (is_nadd y0) (∃ (λ y1 : El num, (∀ (λ y2 : El num, (∀ (λ y3 : El num, (<= (dist ((@̦‚ num num) (* y2 (y0 y3)) (* y3 (y0 y2)))) (* y1 (+ y2 y3))))))))))) x0);
symbol term0 ≔ (λ y0 : El (fun num num), (∃ (λ y1 : El num, (∀ (λ y2 : El num, (∀ (λ y3 : El num, (<= (dist ((@̦‚ num num) (* y2 (y0 y3)) (* y3 (y0 y2)))) (* y1 (+ y2 y3))))))))));
symbol term1 (x0: El (fun num num)) ≔ ((λ y0 : El (fun num num), (∃ (λ y1 : El num, (∀ (λ y2 : El num, (∀ (λ y3 : El num, (<= (dist ((@̦‚ num num) (* y2 (y0 y3)) (* y3 (y0 y2)))) (* y1 (+ y2 y3)))))))))) x0);
