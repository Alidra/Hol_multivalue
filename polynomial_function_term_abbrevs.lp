require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 (x0: El (fun real real)) ≔ ((λ y0 : El (fun real real), (= (polynomial_function y0) (∃ (λ y1 : El num, (∃ (λ y2 : El (fun num real), (∀ (λ y3 : El real, (= (y0 y3) ((@sum num) (… (NUMERAL _0) y1) (λ y4 : El num, (real_mul (y2 y4) (real_pow y3 y4))))))))))))) x0);
symbol term1 (x0: El (fun real real)) ≔ ((λ y0 : El (fun real real), (∃ (λ y1 : El num, (∃ (λ y2 : El (fun num real), (∀ (λ y3 : El real, (= (y0 y3) ((@sum num) (… (NUMERAL _0) y1) (λ y4 : El num, (real_mul (y2 y4) (real_pow y3 y4)))))))))))) x0);
symbol term3 ≔ (∀ (λ y0 : El (fun real real), (= (polynomial_function y0) (∃ (λ y1 : El num, (∃ (λ y2 : El (fun num real), (∀ (λ y3 : El real, (= (y0 y3) ((@sum num) (… (NUMERAL _0) y1) (λ y4 : El num, (real_mul (y2 y4) (real_pow y3 y4))))))))))))));
symbol term0 ≔ (λ y0 : El (fun real real), (∃ (λ y1 : El num, (∃ (λ y2 : El (fun num real), (∀ (λ y3 : El real, (= (y0 y3) ((@sum num) (… (NUMERAL _0) y1) (λ y4 : El num, (real_mul (y2 y4) (real_pow y3 y4))))))))))));
symbol term2 (x0: El (fun real real)) ≔ (∃ (λ y0 : El num, (∃ (λ y1 : El (fun num real), (∀ (λ y2 : El real, (= (x0 y2) ((@sum num) (… (NUMERAL _0) y0) (λ y3 : El num, (real_mul (y1 y3) (real_pow y2 y3)))))))))));
