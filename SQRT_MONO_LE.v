Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_MONO_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LE_LT_spec.
Require Import SQRT_MONO_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1950443 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1950444 : term1 = term2.
Proof. exact (@lem1950443 term1). Qed.
Lemma lem1950445 : term2 = term1.
Proof. exact (SYM (@lem1950444)). Qed.
Lemma lem1950446 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1950449 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1950450 : term5.
Proof. exact (fun h0 : term4 => @lem1950449 h0). Qed.
Lemma lem1950451 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1950452 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1950453 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1950451 h2 (@lem1950452 h1)). Qed.
Lemma lem1950454 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1950453 h1 h0). Qed.
Lemma lem1950455 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1950456 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1950454 h1 (@lem1950455 h2)). Qed.
Lemma lem1950457 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1950456 h0 h1). Qed.
Lemma lem1950458 : term7.
Proof. exact (fun h0 : term5 => @lem1950457 h0). Qed.
Lemma lem1950461 : term5.
Proof. exact (@lem1950458 (@lem1950450)). Qed.
Lemma lem1950487 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1950488 : term8 = term9.
Proof. exact (@lem1950487 term10). Qed.
Lemma lem1950499 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1950500 : term12 = term13.
Proof. exact (MK_COMB (@lem1950499) (@lem1950488)). Qed.
Lemma lem1950503 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1950510 : term4 = term15.
Proof. exact (MK_COMB (@lem1950503) (@lem1950500)). Qed.
Lemma lem1950519 (x : real) (y : real) : ((real_le x y) = (term16 x y)) = ((real_le x y) = (term16 x y)).
Proof. exact (eq_refl ((real_le x y) = (term16 x y))). Qed.
Lemma lem1950520 (x : real) : (term17 x) = (term17 x).
Proof. exact (fun_ext (fun y : real => @lem1950519 x y)). Qed.
Lemma lem1950521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950522 (x : real) : (term18 x) = (term18 x).
Proof. exact (MK_COMB (@lem1950521) (@lem1950520 x)). Qed.
Lemma lem1950523 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1950522 x)). Qed.
Lemma lem1950524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950525 : term10 = term10.
Proof. exact (MK_COMB (@lem1950524) (@lem1950523)). Qed.
Lemma lem1950526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1950527 : term9 = term9.
Proof. exact (MK_COMB (@lem1950526) (@lem1950525)). Qed.
Lemma lem1950532 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1950533 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1950532 x y)). Qed.
Lemma lem1950534 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950535 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1950534) (@lem1950533 x)). Qed.
Lemma lem1950536 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1950535 x)). Qed.
Lemma lem1950537 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950538 : term24 = term24.
Proof. exact (MK_COMB (@lem1950537) (@lem1950536)). Qed.
Lemma lem1950539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1950540 : term11 = term11.
Proof. exact (MK_COMB (@lem1950539) (@lem1950538)). Qed.
Lemma lem1950541 : term13 = term13.
Proof. exact (MK_COMB (@lem1950540) (@lem1950527)). Qed.
Lemma lem1950546 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1950547 (x : real) : (term26 x) = (term26 x).
Proof. exact (fun_ext (fun y : real => @lem1950546 x y)). Qed.
Lemma lem1950548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950549 (x : real) : (term27 x) = (term27 x).
Proof. exact (MK_COMB (@lem1950548) (@lem1950547 x)). Qed.
Lemma lem1950550 : term28 = term28.
Proof. exact (fun_ext (fun x : real => @lem1950549 x)). Qed.
Lemma lem1950551 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950552 : term1 = term1.
Proof. exact (MK_COMB (@lem1950551) (@lem1950550)). Qed.
Lemma lem1950553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1950554 : term3 = term3.
Proof. exact (MK_COMB (@lem1950553) (@lem1950552)). Qed.
Lemma lem1950555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1950556 : term14 = term14.
Proof. exact (MK_COMB (@lem1950555) (@lem1950554)). Qed.
Lemma lem1950557 : term15 = term15.
Proof. exact (MK_COMB (@lem1950556) (@lem1950541)). Qed.
Lemma lem1950606 : term4 = term15.
Proof. exact (TRANS (@lem1950510) (@lem1950557)). Qed.
Lemma lem1950607 : term15 = term4.
Proof. exact (SYM (@lem1950606)). Qed.
Lemma lem1950608 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1950609 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1950610 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1950617 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (@lem17362 (real_le x y) (term31 x y)). Qed.
Lemma lem1950618 (P : real -> Prop) : (term32 P) = (term33 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1950619 (x : real) : (term34 x) = (term35 x).
Proof. exact (@lem1950618 (term26 x)). Qed.
Lemma lem1950620 (x : real) (y : real) : (term36 x y) = (term25 x y).
Proof. exact (eq_refl (term36 x y)). Qed.
Lemma lem1950621 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1950622 (x : real) (y : real) : (term37 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1950621) (@lem1950620 x y)). Qed.
Lemma lem1950623 (x : real) (y : real) : (term37 x y) = (term30 x y).
Proof. exact (TRANS (@lem1950622 x y) (@lem1950617 x y)). Qed.
Lemma lem1950624 (x : real) : (term38 x) = (term39 x).
Proof. exact (fun_ext (fun y : real => @lem1950623 x y)). Qed.
Lemma lem1950625 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1950626 (x : real) : (term35 x) = (term40 x).
Proof. exact (MK_COMB (@lem1950625) (@lem1950624 x)). Qed.
Lemma lem1950627 (x : real) : (term34 x) = (term40 x).
Proof. exact (TRANS (@lem1950619 x) (@lem1950626 x)). Qed.
Lemma lem1950628 (P : real -> Prop) : (term32 P) = (term33 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1950629 : term3 = term41.
Proof. exact (@lem1950628 term28). Qed.
Lemma lem1950630 (x : real) : (term42 x) = (term27 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1950631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1950632 (x : real) : (term43 x) = (term34 x).
Proof. exact (MK_COMB (@lem1950631) (@lem1950630 x)). Qed.
Lemma lem1950633 (x : real) : (term43 x) = (term40 x).
Proof. exact (TRANS (@lem1950632 x) (@lem1950627 x)). Qed.
Lemma lem1950634 : term44 = term45.
Proof. exact (fun_ext (fun x : real => @lem1950633 x)). Qed.
Lemma lem1950635 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1950636 : term41 = term46.
Proof. exact (MK_COMB (@lem1950635) (@lem1950634)). Qed.
Lemma lem1950693 : term3 = term46.
Proof. exact (TRANS (@lem1950629) (@lem1950636)). Qed.
Lemma lem1950694 (h1 : term3) : term46.
Proof. exact (EQ_MP (@lem1950693) (@lem1950608 h1)). Qed.
Lemma lem1950701 (x : real) (y : real) : (term20 x y) = (term47 x y).
Proof. exact (@lem17265 (real_lt x y) (term48 x y)). Qed.
Lemma lem1950702 (x : real) : (term21 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1950701 x y)). Qed.
Lemma lem1950703 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950704 (x : real) : (term22 x) = (term50 x).
Proof. exact (MK_COMB (@lem1950703) (@lem1950702 x)). Qed.
Lemma lem1950705 : term23 = term51.
Proof. exact (fun_ext (fun x : real => @lem1950704 x)). Qed.
Lemma lem1950706 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950763 : term24 = term52.
Proof. exact (MK_COMB (@lem1950706) (@lem1950705)). Qed.
Lemma lem1950764 (h1 : term24) : term52.
Proof. exact (EQ_MP (@lem1950763) (@lem1950609 h1)). Qed.
Lemma lem1950775 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem17160 (real_lt x y) (x = y)). Qed.
Lemma lem1950781 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1950783 (x : real) (y : real) : (term56 x y) = (term56 x y).
Proof. exact (eq_refl (term56 x y)). Qed.
Lemma lem1950784 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1950783 x y) (@lem1950775 x y)). Qed.
Lemma lem1950785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950786 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1950785) (@lem1950784 x y)). Qed.
Lemma lem1950787 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1950786 x y) (@lem1950781 x y)). Qed.
Lemma lem1950788 (x : real) (y : real) : ((real_le x y) = (term16 x y)) = (term61 x y).
Proof. exact (@lem17784 (real_le x y) (term16 x y)). Qed.
Lemma lem1950789 (x : real) (y : real) : ((real_le x y) = (term16 x y)) = (term62 x y).
Proof. exact (TRANS (@lem1950788 x y) (@lem1950787 x y)). Qed.
Lemma lem1950790 (x : real) : (term17 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1950789 x y)). Qed.
Lemma lem1950791 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950792 (x : real) : (term18 x) = (term64 x).
Proof. exact (MK_COMB (@lem1950791) (@lem1950790 x)). Qed.
Lemma lem1950793 : term19 = term65.
Proof. exact (fun_ext (fun x : real => @lem1950792 x)). Qed.
Lemma lem1950794 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950795 : term10 = term66.
Proof. exact (MK_COMB (@lem1950794) (@lem1950793)). Qed.
Lemma lem1950801 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1950802 (P : real -> Prop) (Q : real -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1950801 real P Q). Qed.
Lemma lem1950803 (x : real) : (term71 x) = (term72 x).
Proof. exact (@lem1950802 (term73 x) (term74 x)). Qed.
Lemma lem1950804 (x : real) (y : real) : (term75 x y) = (term58 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1950805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950806 (x : real) (y : real) : (term76 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1950805) (@lem1950804 x y)). Qed.
Lemma lem1950807 (x : real) (y : real) : (term77 x y) = (term55 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem1950808 (x : real) (y : real) : (term78 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1950806 x y) (@lem1950807 x y)). Qed.
Lemma lem1950809 (x : real) : (term79 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1950808 x y)). Qed.
Lemma lem1950810 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950811 (x : real) : (term71 x) = (term64 x).
Proof. exact (MK_COMB (@lem1950810) (@lem1950809 x)). Qed.
Lemma lem1950812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1950813 (x : real) : (term80 x) = (term81 x).
Proof. exact (MK_COMB (@lem1950812) (@lem1950811 x)). Qed.
Lemma lem1950814 (x : real) (y : real) : (term75 x y) = (term58 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1950815 (x : real) : (term82 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1950814 x y)). Qed.
Lemma lem1950816 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950817 (x : real) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1950816) (@lem1950815 x)). Qed.
Lemma lem1950818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950819 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem1950818) (@lem1950817 x)). Qed.
Lemma lem1950820 (x : real) (y : real) : (term77 x y) = (term55 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem1950821 (x : real) : (term87 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1950820 x y)). Qed.
Lemma lem1950822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950823 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1950822) (@lem1950821 x)). Qed.
Lemma lem1950824 (x : real) : (term72 x) = (term90 x).
Proof. exact (MK_COMB (@lem1950819 x) (@lem1950823 x)). Qed.
Lemma lem1950825 (x : real) : ((term71 x) = (term72 x)) = ((term64 x) = (term90 x)).
Proof. exact (MK_COMB (@lem1950813 x) (@lem1950824 x)). Qed.
Lemma lem1950826 (x : real) : (term64 x) = (term90 x).
Proof. exact (EQ_MP (@lem1950825 x) (@lem1950803 x)). Qed.
Lemma lem1950923 : term65 = term91.
Proof. exact (fun_ext (fun x : real => @lem1950826 x)). Qed.
Lemma lem1950924 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950925 : term66 = term92.
Proof. exact (MK_COMB (@lem1950924) (@lem1950923)). Qed.
Lemma lem1950927 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1950928 (P : real -> Prop) (Q : real -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1950927 real P Q). Qed.
Lemma lem1950929 : term93 = term94.
Proof. exact (@lem1950928 term95 term96). Qed.
Lemma lem1950930 (x : real) : (term97 x) = (term84 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1950931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950932 (x : real) : (term98 x) = (term86 x).
Proof. exact (MK_COMB (@lem1950931) (@lem1950930 x)). Qed.
Lemma lem1950933 (x : real) : (term99 x) = (term89 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1950934 (x : real) : (term100 x) = (term90 x).
Proof. exact (MK_COMB (@lem1950932 x) (@lem1950933 x)). Qed.
Lemma lem1950935 : term101 = term91.
Proof. exact (fun_ext (fun x : real => @lem1950934 x)). Qed.
Lemma lem1950936 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950937 : term93 = term92.
Proof. exact (MK_COMB (@lem1950936) (@lem1950935)). Qed.
Lemma lem1950938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1950939 : term102 = term103.
Proof. exact (MK_COMB (@lem1950938) (@lem1950937)). Qed.
Lemma lem1950940 (x : real) : (term97 x) = (term84 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1950941 : term104 = term95.
Proof. exact (fun_ext (fun x : real => @lem1950940 x)). Qed.
Lemma lem1950942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950943 : term105 = term106.
Proof. exact (MK_COMB (@lem1950942) (@lem1950941)). Qed.
Lemma lem1950944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950945 : term107 = term108.
Proof. exact (MK_COMB (@lem1950944) (@lem1950943)). Qed.
Lemma lem1950946 (x : real) : (term99 x) = (term89 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1950947 : term109 = term96.
Proof. exact (fun_ext (fun x : real => @lem1950946 x)). Qed.
Lemma lem1950948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1950949 : term110 = term111.
Proof. exact (MK_COMB (@lem1950948) (@lem1950947)). Qed.
Lemma lem1950950 : term94 = term112.
Proof. exact (MK_COMB (@lem1950945) (@lem1950949)). Qed.
Lemma lem1950951 : (term93 = term94) = (term92 = term112).
Proof. exact (MK_COMB (@lem1950939) (@lem1950950)). Qed.
Lemma lem1950952 : term92 = term112.
Proof. exact (EQ_MP (@lem1950951) (@lem1950929)). Qed.
Lemma lem1951059 : term66 = term112.
Proof. exact (TRANS (@lem1950925) (@lem1950952)). Qed.
Lemma lem1951060 : term10 = term112.
Proof. exact (TRANS (@lem1950795) (@lem1951059)). Qed.
Lemma lem1951061 (h1 : term10) : term112.
Proof. exact (EQ_MP (@lem1951060) (@lem1950610 h1)). Qed.
Lemma lem1951062 (x : real) (h1 : term40 x) : term40 x.
Proof. exact (h1). Qed.
Lemma lem1951082 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1951083 (x : real) : (term49 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1951082 x y)). Qed.
Lemma lem1951084 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951085 (x : real) : (term50 x) = (term50 x).
Proof. exact (MK_COMB (@lem1951084) (@lem1951083 x)). Qed.
Lemma lem1951086 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1951085 x)). Qed.
Lemma lem1951087 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951088 : term52 = term52.
Proof. exact (MK_COMB (@lem1951087) (@lem1951086)). Qed.
Lemma lem1951089 (h1 : term24) : term52.
Proof. exact (EQ_MP (@lem1951088) (@lem1950764 h1)). Qed.
Lemma lem1951112 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1951113 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1951112 x y)). Qed.
Lemma lem1951114 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951115 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem1951114) (@lem1951113 x)). Qed.
Lemma lem1951116 : term96 = term96.
Proof. exact (fun_ext (fun x : real => @lem1951115 x)). Qed.
Lemma lem1951117 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951118 : term111 = term111.
Proof. exact (MK_COMB (@lem1951117) (@lem1951116)). Qed.
Lemma lem1951143 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1951144 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1951143 x y)). Qed.
Lemma lem1951145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951146 (x : real) : (term84 x) = (term84 x).
Proof. exact (MK_COMB (@lem1951145) (@lem1951144 x)). Qed.
Lemma lem1951147 : term95 = term95.
Proof. exact (fun_ext (fun x : real => @lem1951146 x)). Qed.
Lemma lem1951148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951149 : term106 = term106.
Proof. exact (MK_COMB (@lem1951148) (@lem1951147)). Qed.
Lemma lem1951150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1951151 : term108 = term108.
Proof. exact (MK_COMB (@lem1951150) (@lem1951149)). Qed.
Lemma lem1951152 : term112 = term112.
Proof. exact (MK_COMB (@lem1951151) (@lem1951118)). Qed.
Lemma lem1951153 (h1 : term10) : term112.
Proof. exact (EQ_MP (@lem1951152) (@lem1951061 h1)). Qed.
Lemma lem1951173 (x : real) (y : real) (h1 : term30 x y) : term30 x y.
Proof. exact (h1). Qed.
Lemma lem1951176 (h1 : term10) : term111.
Proof. exact (proj2 (@lem1951153 h1)). Qed.
Lemma lem1951177 (h1 : term10) : term106.
Proof. exact (proj1 (@lem1951153 h1)). Qed.
Lemma lem1951185 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1951186 (x : real) : (term49 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1951185 x y)). Qed.
Lemma lem1951187 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951188 (x : real) : (term50 x) = (term50 x).
Proof. exact (MK_COMB (@lem1951187) (@lem1951186 x)). Qed.
Lemma lem1951189 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1951188 x)). Qed.
Lemma lem1951190 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951192 : term52 = term52.
Proof. exact (MK_COMB (@lem1951190) (@lem1951189)). Qed.
Lemma lem1951193 (h1 : term24) : term52.
Proof. exact (EQ_MP (@lem1951192) (@lem1951089 h1)). Qed.
Lemma lem1951219 (x : real) (y : real) : (term58 x y) = (term113 x y).
Proof. exact (@lem19490 (term114 x y) (real_le x y) (term115 x y)). Qed.
Lemma lem1951220 (x : real) : (term73 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1951219 x y)). Qed.
Lemma lem1951221 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951222 (x : real) : (term84 x) = (term117 x).
Proof. exact (MK_COMB (@lem1951221) (@lem1951220 x)). Qed.
Lemma lem1951223 : term95 = term118.
Proof. exact (fun_ext (fun x : real => @lem1951222 x)). Qed.
Lemma lem1951224 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951226 : term106 = term119.
Proof. exact (MK_COMB (@lem1951224) (@lem1951223)). Qed.
Lemma lem1951227 (h1 : term10) : term119.
Proof. exact (EQ_MP (@lem1951226) (@lem1951177 h1)). Qed.
Lemma lem1951241 (x : real) (y : real) : (term55 x y) = (term55 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem1951242 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1951241 x y)). Qed.
Lemma lem1951243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951244 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem1951243) (@lem1951242 x)). Qed.
Lemma lem1951245 : term96 = term96.
Proof. exact (fun_ext (fun x : real => @lem1951244 x)). Qed.
Lemma lem1951246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1951248 : term111 = term111.
Proof. exact (MK_COMB (@lem1951246) (@lem1951245)). Qed.
Lemma lem1951249 (h1 : term10) : term111.
Proof. exact (EQ_MP (@lem1951248) (@lem1951176 h1)). Qed.
Lemma lem1951250 (_27378 : real) (h1 : term24) : term120 _27378.
Proof. exact (@lem1951193 h1 _27378). Qed.
Lemma lem1951251 (_27378 : real) : (term120 _27378) = (term50 _27378).
Proof. exact (eq_refl (term120 _27378)). Qed.
Lemma lem1951252 (_27378 : real) (h1 : term24) : term50 _27378.
Proof. exact (EQ_MP (@lem1951251 _27378) (@lem1951250 _27378 h1)). Qed.
Lemma lem1951253 (_27378 : real) (_27379 : real) (h1 : term24) : term121 _27378 _27379.
Proof. exact (@lem1951252 _27378 h1 _27379). Qed.
Lemma lem1951254 (_27378 : real) (_27379 : real) : (term121 _27378 _27379) = (term47 _27378 _27379).
Proof. exact (eq_refl (term121 _27378 _27379)). Qed.
Lemma lem1951256 (_27380 : real) (h1 : term10) : term122 _27380.
Proof. exact (@lem1951227 h1 _27380). Qed.
Lemma lem1951257 (_27380 : real) : (term122 _27380) = (term117 _27380).
Proof. exact (eq_refl (term122 _27380)). Qed.
Lemma lem1951258 (_27380 : real) (h1 : term10) : term117 _27380.
Proof. exact (EQ_MP (@lem1951257 _27380) (@lem1951256 _27380 h1)). Qed.
Lemma lem1951259 (_27380 : real) (_27381 : real) (h1 : term10) : term123 _27380 _27381.
Proof. exact (@lem1951258 _27380 h1 _27381). Qed.
Lemma lem1951260 (_27380 : real) (_27381 : real) : (term123 _27380 _27381) = (term113 _27380 _27381).
Proof. exact (eq_refl (term123 _27380 _27381)). Qed.
Lemma lem1951261 (_27380 : real) (_27381 : real) (h1 : term10) : term113 _27380 _27381.
Proof. exact (EQ_MP (@lem1951260 _27380 _27381) (@lem1951259 _27380 _27381 h1)). Qed.
Lemma lem1951262 (_27382 : real) (h1 : term10) : term99 _27382.
Proof. exact (@lem1951249 h1 _27382). Qed.
Lemma lem1951263 (_27382 : real) : (term99 _27382) = (term89 _27382).
Proof. exact (eq_refl (term99 _27382)). Qed.
Lemma lem1951264 (_27382 : real) (h1 : term10) : term89 _27382.
Proof. exact (EQ_MP (@lem1951263 _27382) (@lem1951262 _27382 h1)). Qed.
Lemma lem1951265 (_27382 : real) (_27383 : real) (h1 : term10) : term77 _27382 _27383.
Proof. exact (@lem1951264 _27382 h1 _27383). Qed.
Lemma lem1951266 (_27382 : real) (_27383 : real) : (term77 _27382 _27383) = (term55 _27382 _27383).
Proof. exact (eq_refl (term77 _27382 _27383)). Qed.
Lemma lem1951275 (_27378 : real) (_27379 : real) (h1 : term24) : term47 _27378 _27379.
Proof. exact (EQ_MP (@lem1951254 _27378 _27379) (@lem1951253 _27378 _27379 h1)). Qed.
Lemma lem1951279 (x : real) (y : real) (h1 : term30 x y) : term124 x y.
Proof. exact (proj2 (@lem1951173 x y h1)). Qed.
Lemma lem1951289 (_27382 : real) (_27383 : real) (h1 : term10) : term55 _27382 _27383.
Proof. exact (EQ_MP (@lem1951266 _27382 _27383) (@lem1951265 _27382 _27383 h1)). Qed.
Lemma lem1951295 (_27380 : real) (_27381 : real) (h1 : term10) : term125 _27380 _27381.
Proof. exact (proj1 (@lem1951261 _27380 _27381 h1)). Qed.
Lemma lem1951301 (_27380 : real) (_27381 : real) (h1 : term10) : term126 _27380 _27381.
Proof. exact (proj2 (@lem1951261 _27380 _27381 h1)). Qed.
Lemma lem1951340 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1951341 (_27392 : real) (_27393 : real) (h1 : _27392 = _27393) : _27392 = _27393.
Proof. exact (h1). Qed.
Lemma lem1951342 (_27392 : real) (_27393 : real) (h1 : _27392 = _27393) : (sqrt _27392) = (sqrt _27393).
Proof. exact (MK_COMB (@lem1951340) (@lem1951341 _27392 _27393 h1)). Qed.
Lemma lem1951343 (_27392 : real) (_27393 : real) : term127 _27392 _27393.
Proof. exact (fun h0 : _27392 = _27393 => @lem1951342 _27392 _27393 h0). Qed.
Lemma lem1951345 (a : Prop) (b : Prop) : (a -> b) = (term128 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1951346 (_27392 : real) (_27393 : real) : (term127 _27392 _27393) = (term129 _27392 _27393).
Proof. exact (@lem1951345 (_27392 = _27393) ((sqrt _27392) = (sqrt _27393))). Qed.
Lemma lem1951347 (_27392 : real) (_27393 : real) : term129 _27392 _27393.
Proof. exact (EQ_MP (@lem1951346 _27392 _27393) (@lem1951343 _27392 _27393)). Qed.
Lemma lem1951351 (x : real) (y : real) (h1 : term30 x y) : real_le x y.
Proof. exact (proj1 (@lem1951173 x y h1)). Qed.
Lemma lem1951352 (x : real) (y : real) (h1 : term30 x y) : term130 x y.
Proof. exact (fun h0 : term131 x y => @lem1951351 x y h1). Qed.
Lemma lem1951354 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1951355 (x : real) (y : real) : (term130 x y) = (real_le x y).
Proof. exact (@lem1951354 (real_le x y)). Qed.
Lemma lem1951356 (x : real) (y : real) (h1 : term30 x y) : real_le x y.
Proof. exact (EQ_MP (@lem1951355 x y) (@lem1951352 x y h1)). Qed.
Lemma lem1951359 (x : real) (y : real) (h1 : term124 x y) : term124 x y.
Proof. exact (h1). Qed.
Lemma lem1951360 (x : real) (y : real) (h1 : term124 x y) : term133 x y.
Proof. exact (fun h0 : term31 x y => @lem1951359 x y h1). Qed.
Lemma lem1951362 (p : Prop) : (term134 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1951363 (x : real) (y : real) : (term133 x y) = (term124 x y).
Proof. exact (@lem1951362 (term31 x y)). Qed.
Lemma lem1951364 (x : real) (y : real) (h1 : term124 x y) : term124 x y.
Proof. exact (EQ_MP (@lem1951363 x y) (@lem1951360 x y h1)). Qed.
Lemma lem1951375 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1951376 (_27380 : real) (_27381 : real) : (term135 _27380 _27381) = (term125 _27380 _27381).
Proof. exact (@lem1951375 (real_le _27380 _27381) (term114 _27380 _27381)). Qed.
Lemma lem1951382 (_27380 : real) (_27381 : real) : (term136 _27380 _27381) = (term136 _27380 _27381).
Proof. exact (eq_refl (term136 _27380 _27381)). Qed.
Lemma lem1951383 (_27380 : real) (_27381 : real) : ((term125 _27380 _27381) = (term135 _27380 _27381)) = ((term125 _27380 _27381) = (term125 _27380 _27381)).
Proof. exact (MK_COMB (@lem1951382 _27380 _27381) (@lem1951376 _27380 _27381)). Qed.
Lemma lem1951385 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1951386 (x : Prop) : (x = x) = True.
Proof. exact (@lem1951385 Prop x). Qed.
Lemma lem1951387 (_27380 : real) (_27381 : real) : ((term125 _27380 _27381) = (term125 _27380 _27381)) = True.
Proof. exact (@lem1951386 (term125 _27380 _27381)). Qed.
Lemma lem1951388 (_27380 : real) (_27381 : real) : ((term125 _27380 _27381) = (term135 _27380 _27381)) = True.
Proof. exact (TRANS (@lem1951383 _27380 _27381) (@lem1951387 _27380 _27381)). Qed.
Lemma lem1951389 (_27380 : real) (_27381 : real) : True = ((term125 _27380 _27381) = (term135 _27380 _27381)).
Proof. exact (SYM (@lem1951388 _27380 _27381)). Qed.
Lemma lem1951390 (_27380 : real) (_27381 : real) : (term125 _27380 _27381) = (term135 _27380 _27381).
Proof. exact (EQ_MP (@lem1951389 _27380 _27381) (@lem0)). Qed.
Lemma lem1951391 (_27380 : real) (_27381 : real) (h1 : term10) : term135 _27380 _27381.
Proof. exact (EQ_MP (@lem1951390 _27380 _27381) (@lem1951295 _27380 _27381 h1)). Qed.
Lemma lem1951393 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1951396 (_27380 : real) (_27381 : real) : (term135 _27380 _27381) = (term138 _27380 _27381).
Proof. exact (@lem1951393 (real_le _27380 _27381) (term114 _27380 _27381)). Qed.
Lemma lem1951399 (_27380 : real) (_27381 : real) (h1 : term10) : term138 _27380 _27381.
Proof. exact (EQ_MP (@lem1951396 _27380 _27381) (@lem1951391 _27380 _27381 h1)). Qed.
Lemma lem1951400 (x : real) (y : real) (h1 : term10) : term139 x y.
Proof. exact (@lem1951399 (sqrt x) (sqrt y) h1). Qed.
Lemma lem1951403 (x : real) (y : real) (h1 : term10) (h2 : term124 x y) : term140 x y.
Proof. exact (@lem1951400 x y h1 (@lem1951364 x y h2)). Qed.
Lemma lem1951404 (x : real) (y : real) (h1 : term10) (h2 : term124 x y) : term141 x y.
Proof. exact (fun h0 : term48 x y => @lem1951403 x y h1 h2). Qed.
Lemma lem1951406 (p : Prop) : (term134 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1951407 (x : real) (y : real) : (term141 x y) = (term140 x y).
Proof. exact (@lem1951406 (term48 x y)). Qed.
Lemma lem1951408 (x : real) (y : real) (h1 : term10) (h2 : term124 x y) : term140 x y.
Proof. exact (EQ_MP (@lem1951407 x y) (@lem1951404 x y h1 h2)). Qed.
Lemma lem1951410 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1951413 (_27378 : real) (_27379 : real) : (term47 _27378 _27379) = (term142 _27378 _27379).
Proof. exact (@lem1951410 (term48 _27378 _27379) (term114 _27378 _27379)). Qed.
Lemma lem1951416 (_27378 : real) (_27379 : real) (h1 : term24) : term142 _27378 _27379.
Proof. exact (EQ_MP (@lem1951413 _27378 _27379) (@lem1951275 _27378 _27379 h1)). Qed.
Lemma lem1951417 (x : real) (y : real) (h1 : term24) : term142 x y.
Proof. exact (@lem1951416 x y h1). Qed.
Lemma lem1951420 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) : term114 x y.
Proof. exact (@lem1951417 x y h2 (@lem1951408 x y h1 h3)). Qed.
Lemma lem1951421 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) : term143 x y.
Proof. exact (fun h0 : real_lt x y => @lem1951420 x y h1 h2 h3). Qed.
Lemma lem1951423 (p : Prop) : (term134 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1951424 (x : real) (y : real) : (term143 x y) = (term114 x y).
Proof. exact (@lem1951423 (real_lt x y)). Qed.
Lemma lem1951425 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) : term114 x y.
Proof. exact (EQ_MP (@lem1951424 x y) (@lem1951421 x y h1 h2 h3)). Qed.
Lemma lem1951431 (q : Prop) (p : Prop) (r : Prop) : (term144 p q r) = (term144 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1951432 (_27382 : real) (_27383 : real) : (term55 _27382 _27383) = (term145 _27382 _27383).
Proof. exact (@lem1951431 (real_lt _27382 _27383) (term131 _27382 _27383) (_27382 = _27383)). Qed.
Lemma lem1951446 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1951447 (_27382 : real) (_27383 : real) : (term146 _27382 _27383) = (term147 _27382 _27383).
Proof. exact (@lem1951446 (_27382 = _27383) (term131 _27382 _27383)). Qed.
Lemma lem1951455 (_27382 : real) (_27383 : real) : (term148 _27382 _27383) = (term148 _27382 _27383).
Proof. exact (eq_refl (term148 _27382 _27383)). Qed.
Lemma lem1951456 (_27382 : real) (_27383 : real) : (term145 _27382 _27383) = (term149 _27382 _27383).
Proof. exact (MK_COMB (@lem1951455 _27382 _27383) (@lem1951447 _27382 _27383)). Qed.
Lemma lem1951460 (q : Prop) (p : Prop) (r : Prop) : (term144 p q r) = (term144 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1951461 (_27382 : real) (_27383 : real) : (term149 _27382 _27383) = (term150 _27382 _27383).
Proof. exact (@lem1951460 (_27382 = _27383) (real_lt _27382 _27383) (term131 _27382 _27383)). Qed.
Lemma lem1951479 (_27382 : real) (_27383 : real) : (term145 _27382 _27383) = (term150 _27382 _27383).
Proof. exact (TRANS (@lem1951456 _27382 _27383) (@lem1951461 _27382 _27383)). Qed.
Lemma lem1951480 (_27382 : real) (_27383 : real) : (term55 _27382 _27383) = (term150 _27382 _27383).
Proof. exact (TRANS (@lem1951432 _27382 _27383) (@lem1951479 _27382 _27383)). Qed.
Lemma lem1951481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1951482 (_27382 : real) (_27383 : real) : (term151 _27382 _27383) = (term152 _27382 _27383).
Proof. exact (MK_COMB (@lem1951481) (@lem1951480 _27382 _27383)). Qed.
Lemma lem1951498 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1951499 (_27382 : real) (_27383 : real) : (term153 _27382 _27383) = (term154 _27382 _27383).
Proof. exact (@lem1951498 (real_lt _27382 _27383) (term131 _27382 _27383)). Qed.
Lemma lem1951505 (_27382 : real) (_27383 : real) : (term155 _27382 _27383) = (term155 _27382 _27383).
Proof. exact (eq_refl (term155 _27382 _27383)). Qed.
Lemma lem1951506 (_27382 : real) (_27383 : real) : (term156 _27382 _27383) = (term150 _27382 _27383).
Proof. exact (MK_COMB (@lem1951505 _27382 _27383) (@lem1951499 _27382 _27383)). Qed.
Lemma lem1951517 (_27382 : real) (_27383 : real) : ((term55 _27382 _27383) = (term156 _27382 _27383)) = ((term150 _27382 _27383) = (term150 _27382 _27383)).
Proof. exact (MK_COMB (@lem1951482 _27382 _27383) (@lem1951506 _27382 _27383)). Qed.
Lemma lem1951519 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1951520 (x : Prop) : (x = x) = True.
Proof. exact (@lem1951519 Prop x). Qed.
Lemma lem1951521 (_27382 : real) (_27383 : real) : ((term150 _27382 _27383) = (term150 _27382 _27383)) = True.
Proof. exact (@lem1951520 (term150 _27382 _27383)). Qed.
Lemma lem1951522 (_27382 : real) (_27383 : real) : ((term55 _27382 _27383) = (term156 _27382 _27383)) = True.
Proof. exact (TRANS (@lem1951517 _27382 _27383) (@lem1951521 _27382 _27383)). Qed.
Lemma lem1951523 (_27382 : real) (_27383 : real) : True = ((term55 _27382 _27383) = (term156 _27382 _27383)).
Proof. exact (SYM (@lem1951522 _27382 _27383)). Qed.
Lemma lem1951524 (_27382 : real) (_27383 : real) : (term55 _27382 _27383) = (term156 _27382 _27383).
Proof. exact (EQ_MP (@lem1951523 _27382 _27383) (@lem0)). Qed.
Lemma lem1951525 (_27382 : real) (_27383 : real) (h1 : term10) : term156 _27382 _27383.
Proof. exact (EQ_MP (@lem1951524 _27382 _27383) (@lem1951289 _27382 _27383 h1)). Qed.
Lemma lem1951527 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1951528 (_27382 : real) (_27383 : real) : (term156 _27382 _27383) = (term157 _27382 _27383).
Proof. exact (@lem1951527 (term153 _27382 _27383) (_27382 = _27383)). Qed.
Lemma lem1951530 (a : Prop) (b : Prop) : (term158 a b) = (term159 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1951531 (_27382 : real) (_27383 : real) : (term160 _27382 _27383) = (term161 _27382 _27383).
Proof. exact (@lem1951530 (term131 _27382 _27383) (real_lt _27382 _27383)). Qed.
Lemma lem1951533 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1951534 (_27382 : real) (_27383 : real) : (term163 _27382 _27383) = (real_le _27382 _27383).
Proof. exact (@lem1951533 (real_le _27382 _27383)). Qed.
Lemma lem1951535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1951536 (_27382 : real) (_27383 : real) : (term164 _27382 _27383) = (term165 _27382 _27383).
Proof. exact (MK_COMB (@lem1951535) (@lem1951534 _27382 _27383)). Qed.
Lemma lem1951537 (_27382 : real) (_27383 : real) : (term114 _27382 _27383) = (term114 _27382 _27383).
Proof. exact (eq_refl (term114 _27382 _27383)). Qed.
Lemma lem1951538 (_27382 : real) (_27383 : real) : (term161 _27382 _27383) = (term166 _27382 _27383).
Proof. exact (MK_COMB (@lem1951536 _27382 _27383) (@lem1951537 _27382 _27383)). Qed.
Lemma lem1951539 (_27382 : real) (_27383 : real) : (term160 _27382 _27383) = (term166 _27382 _27383).
Proof. exact (TRANS (@lem1951531 _27382 _27383) (@lem1951538 _27382 _27383)). Qed.
Lemma lem1951540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1951541 (_27382 : real) (_27383 : real) : (term167 _27382 _27383) = (term168 _27382 _27383).
Proof. exact (MK_COMB (@lem1951540) (@lem1951539 _27382 _27383)). Qed.
Lemma lem1951542 (_27382 : real) (_27383 : real) : (_27382 = _27383) = (_27382 = _27383).
Proof. exact (eq_refl (_27382 = _27383)). Qed.
Lemma lem1951543 (_27382 : real) (_27383 : real) : (term157 _27382 _27383) = (term169 _27382 _27383).
Proof. exact (MK_COMB (@lem1951541 _27382 _27383) (@lem1951542 _27382 _27383)). Qed.
Lemma lem1951544 (_27382 : real) (_27383 : real) : (term156 _27382 _27383) = (term169 _27382 _27383).
Proof. exact (TRANS (@lem1951528 _27382 _27383) (@lem1951543 _27382 _27383)). Qed.
Lemma lem1951546 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : term166 x y.
Proof. exact (conj (@lem1951356 x y h4) (@lem1951425 x y h1 h2 h3)). Qed.
Lemma lem1951548 (_27382 : real) (_27383 : real) (h1 : term10) : term169 _27382 _27383.
Proof. exact (EQ_MP (@lem1951544 _27382 _27383) (@lem1951525 _27382 _27383 h1)). Qed.
Lemma lem1951549 (x : real) (y : real) (h1 : term10) : term169 x y.
Proof. exact (@lem1951548 x y h1). Qed.
Lemma lem1951552 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : x = y.
Proof. exact (@lem1951549 x y h1 (@lem1951546 x y h1 h2 h3 h4)). Qed.
Lemma lem1951553 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : term170 x y.
Proof. exact (fun h0 : term115 x y => @lem1951552 x y h1 h2 h3 h4). Qed.
Lemma lem1951555 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1951556 (x : real) (y : real) : (term170 x y) = (x = y).
Proof. exact (@lem1951555 (x = y)). Qed.
Lemma lem1951557 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : x = y.
Proof. exact (EQ_MP (@lem1951556 x y) (@lem1951553 x y h1 h2 h3 h4)). Qed.
Lemma lem1951563 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1951564 (_27392 : real) (_27393 : real) : (term129 _27392 _27393) = (term171 _27392 _27393).
Proof. exact (@lem1951563 ((sqrt _27392) = (sqrt _27393)) (term115 _27392 _27393)). Qed.
Lemma lem1951574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1951575 (_27392 : real) (_27393 : real) : (term172 _27392 _27393) = (term173 _27392 _27393).
Proof. exact (MK_COMB (@lem1951574) (@lem1951564 _27392 _27393)). Qed.
Lemma lem1951585 (_27392 : real) (_27393 : real) : (term171 _27392 _27393) = (term171 _27392 _27393).
Proof. exact (eq_refl (term171 _27392 _27393)). Qed.
Lemma lem1951586 (_27392 : real) (_27393 : real) : ((term129 _27392 _27393) = (term171 _27392 _27393)) = ((term171 _27392 _27393) = (term171 _27392 _27393)).
Proof. exact (MK_COMB (@lem1951575 _27392 _27393) (@lem1951585 _27392 _27393)). Qed.
Lemma lem1951588 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1951589 (x : Prop) : (x = x) = True.
Proof. exact (@lem1951588 Prop x). Qed.
Lemma lem1951590 (_27392 : real) (_27393 : real) : ((term171 _27392 _27393) = (term171 _27392 _27393)) = True.
Proof. exact (@lem1951589 (term171 _27392 _27393)). Qed.
Lemma lem1951591 (_27392 : real) (_27393 : real) : ((term129 _27392 _27393) = (term171 _27392 _27393)) = True.
Proof. exact (TRANS (@lem1951586 _27392 _27393) (@lem1951590 _27392 _27393)). Qed.
Lemma lem1951592 (_27392 : real) (_27393 : real) : True = ((term129 _27392 _27393) = (term171 _27392 _27393)).
Proof. exact (SYM (@lem1951591 _27392 _27393)). Qed.
Lemma lem1951593 (_27392 : real) (_27393 : real) : (term129 _27392 _27393) = (term171 _27392 _27393).
Proof. exact (EQ_MP (@lem1951592 _27392 _27393) (@lem0)). Qed.
Lemma lem1951594 (_27392 : real) (_27393 : real) : term171 _27392 _27393.
Proof. exact (EQ_MP (@lem1951593 _27392 _27393) (@lem1951347 _27392 _27393)). Qed.
Lemma lem1951596 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1951597 (_27392 : real) (_27393 : real) : (term171 _27392 _27393) = (term174 _27392 _27393).
Proof. exact (@lem1951596 (term115 _27392 _27393) ((sqrt _27392) = (sqrt _27393))). Qed.
Lemma lem1951599 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1951600 (_27392 : real) (_27393 : real) : (term175 _27392 _27393) = (_27392 = _27393).
Proof. exact (@lem1951599 (_27392 = _27393)). Qed.
Lemma lem1951601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1951602 (_27392 : real) (_27393 : real) : (term176 _27392 _27393) = (term177 _27392 _27393).
Proof. exact (MK_COMB (@lem1951601) (@lem1951600 _27392 _27393)). Qed.
Lemma lem1951603 (_27392 : real) (_27393 : real) : ((sqrt _27392) = (sqrt _27393)) = ((sqrt _27392) = (sqrt _27393)).
Proof. exact (eq_refl ((sqrt _27392) = (sqrt _27393))). Qed.
Lemma lem1951604 (_27392 : real) (_27393 : real) : (term174 _27392 _27393) = (term127 _27392 _27393).
Proof. exact (MK_COMB (@lem1951602 _27392 _27393) (@lem1951603 _27392 _27393)). Qed.
Lemma lem1951605 (_27392 : real) (_27393 : real) : (term171 _27392 _27393) = (term127 _27392 _27393).
Proof. exact (TRANS (@lem1951597 _27392 _27393) (@lem1951604 _27392 _27393)). Qed.
Lemma lem1951608 (_27392 : real) (_27393 : real) : term127 _27392 _27393.
Proof. exact (EQ_MP (@lem1951605 _27392 _27393) (@lem1951594 _27392 _27393)). Qed.
Lemma lem1951609 (x : real) (y : real) : term127 x y.
Proof. exact (@lem1951608 x y). Qed.
Lemma lem1951612 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : (sqrt x) = (sqrt y).
Proof. exact (@lem1951609 x y (@lem1951557 x y h1 h2 h3 h4)). Qed.
Lemma lem1951613 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : term178 x y.
Proof. exact (fun h0 : term179 x y => @lem1951612 x y h1 h2 h3 h4). Qed.
Lemma lem1951615 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1951616 (x : real) (y : real) : (term178 x y) = ((sqrt x) = (sqrt y)).
Proof. exact (@lem1951615 ((sqrt x) = (sqrt y))). Qed.
Lemma lem1951617 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : (sqrt x) = (sqrt y).
Proof. exact (EQ_MP (@lem1951616 x y) (@lem1951613 x y h1 h2 h3 h4)). Qed.
Lemma lem1951619 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1951620 (_27380 : real) (_27381 : real) : (term126 _27380 _27381) = (term180 _27380 _27381).
Proof. exact (@lem1951619 (term115 _27380 _27381) (real_le _27380 _27381)). Qed.
Lemma lem1951622 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1951623 (_27380 : real) (_27381 : real) : (term175 _27380 _27381) = (_27380 = _27381).
Proof. exact (@lem1951622 (_27380 = _27381)). Qed.
Lemma lem1951624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1951625 (_27380 : real) (_27381 : real) : (term176 _27380 _27381) = (term177 _27380 _27381).
Proof. exact (MK_COMB (@lem1951624) (@lem1951623 _27380 _27381)). Qed.
Lemma lem1951626 (_27380 : real) (_27381 : real) : (real_le _27380 _27381) = (real_le _27380 _27381).
Proof. exact (eq_refl (real_le _27380 _27381)). Qed.
Lemma lem1951627 (_27380 : real) (_27381 : real) : (term180 _27380 _27381) = (term181 _27380 _27381).
Proof. exact (MK_COMB (@lem1951625 _27380 _27381) (@lem1951626 _27380 _27381)). Qed.
Lemma lem1951628 (_27380 : real) (_27381 : real) : (term126 _27380 _27381) = (term181 _27380 _27381).
Proof. exact (TRANS (@lem1951620 _27380 _27381) (@lem1951627 _27380 _27381)). Qed.
Lemma lem1951631 (_27380 : real) (_27381 : real) (h1 : term10) : term181 _27380 _27381.
Proof. exact (EQ_MP (@lem1951628 _27380 _27381) (@lem1951301 _27380 _27381 h1)). Qed.
Lemma lem1951632 (x : real) (y : real) (h1 : term10) : term182 x y.
Proof. exact (@lem1951631 (sqrt x) (sqrt y) h1). Qed.
Lemma lem1951635 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term124 x y) (h4 : term30 x y) : term31 x y.
Proof. exact (@lem1951632 x y h1 (@lem1951617 x y h1 h2 h3 h4)). Qed.
Lemma lem1951636 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : term183 x y.
Proof. exact (fun h0 : term124 x y => @lem1951635 x y h1 h2 h0 h3). Qed.
Lemma lem1951638 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1951639 (x : real) (y : real) : (term183 x y) = (term31 x y).
Proof. exact (@lem1951638 (term31 x y)). Qed.
Lemma lem1951640 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : term31 x y.
Proof. exact (EQ_MP (@lem1951639 x y) (@lem1951636 x y h1 h2 h3)). Qed.
Lemma lem1951643 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1951645 (x : real) (y : real) : (term124 x y) = (term184 x y).
Proof. exact (@lem1951643 (term31 x y)). Qed.
Lemma lem1951648 (x : real) (y : real) (h1 : term30 x y) : term184 x y.
Proof. exact (EQ_MP (@lem1951645 x y) (@lem1951279 x y h1)). Qed.
Lemma lem1951651 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (@lem1951648 x y h3 (@lem1951640 x y h1 h2 h3)). Qed.
Lemma lem1951652 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : term185.
Proof. exact (fun h0 : ~ False => @lem1951651 x y h1 h2 h3). Qed.
Lemma lem1951654 (p : Prop) : (term132 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1951655 : term185 = False.
Proof. exact (@lem1951654 False). Qed.
Lemma lem1951656 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (EQ_MP (@lem1951655) (@lem1951652 x y h1 h2 h3)). Qed.
Lemma lem1951657 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : (term30 x y) = False.
Proof. exact (prop_ext (fun h4 : term30 x y => @lem1951656 x y h1 h2 h3) (fun h4 : False => @lem1951173 x y h3)). Qed.
Lemma lem1951658 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (EQ_MP (@lem1951657 x y h1 h2 h3) (@lem1951173 x y h3)). Qed.
Lemma lem1951659 (x : real) (h1 : term10) (h2 : term24) (h3 : term40 x) : False.
Proof. exact (ex_elim (@lem1951062 x h3) (fun y : real => fun h0 : term39 x y => @lem1951658 x y h1 h2 h0)). Qed.
Lemma lem1951660 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1950694 h3) (fun x : real => fun h0 : term45 x => @lem1951659 x h1 h2 h0)). Qed.
Lemma lem1951661 (h1 : term24) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1951660 h0 h1 h2). Qed.
Lemma lem1951662 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1951663 (h1 : term24) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1951662) (@lem1951661 h1 h2)). Qed.
Lemma lem1951664 (h1 : term3) : term13.
Proof. exact (fun h0 : term24 => @lem1951663 h0 h1). Qed.
Lemma lem1951665 : term15.
Proof. exact (fun h0 : term3 => @lem1951664 h0). Qed.
Lemma lem1951666 : term4.
Proof. exact (EQ_MP (@lem1950607) (@lem1951665)). Qed.
Lemma lem1951668 : term4.
Proof. exact (@lem1950461 (@lem1951666)). Qed.
Lemma lem1951669 (h1 : term3) : term12.
Proof. exact (@lem1951668 (@lem1950446 h1)). Qed.
Lemma lem1951670 (h1 : term3) : term8.
Proof. exact (@lem1951669 h1 (@lem1950431)). Qed.
Lemma lem1951671 (h1 : term3) : False.
Proof. exact (@lem1951670 h1 (@lem1376325)). Qed.
Lemma lem1951672 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1951671 h1) (fun h2 : False => @lem1950446 h1)). Qed.
Lemma lem1951673 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1951672 h1) (@lem1950446 h1)). Qed.
Lemma lem1951674 : term2.
Proof. exact (fun h0 : term3 => @lem1951673 h0). Qed.
Lemma lem1951675 : term1.
Proof. exact (EQ_MP (@lem1950445) (@lem1951674)). Qed.
