Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ADD_RINV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338238_spec.
Require Import thm1338588_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm69_spec.
Lemma lem1352542 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1352543 : term1 = term2.
Proof. exact (@lem1352542 term1). Qed.
Lemma lem1352544 : term2 = term1.
Proof. exact (SYM (@lem1352543)). Qed.
Lemma lem1352545 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1352548 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1352549 : term5.
Proof. exact (fun h0 : term4 => @lem1352548 h0). Qed.
Lemma lem1352550 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1352551 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1352552 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1352550 h2 (@lem1352551 h1)). Qed.
Lemma lem1352553 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1352552 h1 h0). Qed.
Lemma lem1352554 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1352555 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1352553 h1 (@lem1352554 h2)). Qed.
Lemma lem1352556 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1352555 h0 h1). Qed.
Lemma lem1352557 : term7.
Proof. exact (fun h0 : term5 => @lem1352556 h0). Qed.
Lemma lem1352560 : term5.
Proof. exact (@lem1352557 (@lem1352549)). Qed.
Lemma lem1352574 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1352575 : term8 = term9.
Proof. exact (@lem1352574 term10). Qed.
Lemma lem1352584 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1352585 : term12 = term13.
Proof. exact (MK_COMB (@lem1352584) (@lem1352575)). Qed.
Lemma lem1352588 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1352595 : term4 = term15.
Proof. exact (MK_COMB (@lem1352588) (@lem1352585)). Qed.
Lemma lem1352596 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1352597 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1352596 y x)). Qed.
Lemma lem1352598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352599 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1352598) (@lem1352597 x)). Qed.
Lemma lem1352600 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1352599 x)). Qed.
Lemma lem1352601 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352602 : term10 = term10.
Proof. exact (MK_COMB (@lem1352601) (@lem1352600)). Qed.
Lemma lem1352603 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1352604 : term9 = term9.
Proof. exact (MK_COMB (@lem1352603) (@lem1352602)). Qed.
Lemma lem1352605 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1352606 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1352605 x)). Qed.
Lemma lem1352607 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352608 : term22 = term22.
Proof. exact (MK_COMB (@lem1352607) (@lem1352606)). Qed.
Lemma lem1352609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1352610 : term11 = term11.
Proof. exact (MK_COMB (@lem1352609) (@lem1352608)). Qed.
Lemma lem1352611 : term13 = term13.
Proof. exact (MK_COMB (@lem1352610) (@lem1352604)). Qed.
Lemma lem1352612 (x : real) : ((term23 x) = term20) = ((term23 x) = term20).
Proof. exact (eq_refl ((term23 x) = term20)). Qed.
Lemma lem1352613 : term24 = term24.
Proof. exact (fun_ext (fun x : real => @lem1352612 x)). Qed.
Lemma lem1352614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352615 : term1 = term1.
Proof. exact (MK_COMB (@lem1352614) (@lem1352613)). Qed.
Lemma lem1352616 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1352617 : term3 = term3.
Proof. exact (MK_COMB (@lem1352616) (@lem1352615)). Qed.
Lemma lem1352618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1352619 : term14 = term14.
Proof. exact (MK_COMB (@lem1352618) (@lem1352617)). Qed.
Lemma lem1352620 : term15 = term15.
Proof. exact (MK_COMB (@lem1352619) (@lem1352611)). Qed.
Lemma lem1352651 : term4 = term15.
Proof. exact (TRANS (@lem1352595) (@lem1352620)). Qed.
Lemma lem1352652 : term15 = term4.
Proof. exact (SYM (@lem1352651)). Qed.
Lemma lem1352653 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1352654 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1352655 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1352657 (P : real -> Prop) : (term25 P) = (term26 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1352658 : term3 = term27.
Proof. exact (@lem1352657 term24). Qed.
Lemma lem1352659 (x : real) : (term28 x) = ((term23 x) = term20).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1352660 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1352662 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1352660) (@lem1352659 x)). Qed.
Lemma lem1352663 : term31 = term32.
Proof. exact (fun_ext (fun x : real => @lem1352662 x)). Qed.
Lemma lem1352664 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1352665 : term27 = term33.
Proof. exact (MK_COMB (@lem1352664) (@lem1352663)). Qed.
Lemma lem1352674 : term3 = term33.
Proof. exact (TRANS (@lem1352658) (@lem1352665)). Qed.
Lemma lem1352675 (h1 : term3) : term33.
Proof. exact (EQ_MP (@lem1352674) (@lem1352653 h1)). Qed.
Lemma lem1352676 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1352677 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1352676 x)). Qed.
Lemma lem1352678 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352687 : term22 = term22.
Proof. exact (MK_COMB (@lem1352678) (@lem1352677)). Qed.
Lemma lem1352688 (h1 : term22) : term22.
Proof. exact (EQ_MP (@lem1352687) (@lem1352654 h1)). Qed.
Lemma lem1352689 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1352690 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1352689 y x)). Qed.
Lemma lem1352691 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352692 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1352691) (@lem1352690 x)). Qed.
Lemma lem1352693 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1352692 x)). Qed.
Lemma lem1352694 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352707 : term10 = term10.
Proof. exact (MK_COMB (@lem1352694) (@lem1352693)). Qed.
Lemma lem1352708 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1352707) (@lem1352655 h1)). Qed.
Lemma lem1352724 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1352725 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1352724 x)). Qed.
Lemma lem1352726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352727 : term22 = term22.
Proof. exact (MK_COMB (@lem1352726) (@lem1352725)). Qed.
Lemma lem1352728 (h1 : term22) : term22.
Proof. exact (EQ_MP (@lem1352727) (@lem1352688 h1)). Qed.
Lemma lem1352741 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1352742 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1352741 y x)). Qed.
Lemma lem1352743 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352744 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1352743) (@lem1352742 x)). Qed.
Lemma lem1352745 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1352744 x)). Qed.
Lemma lem1352746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352747 : term10 = term10.
Proof. exact (MK_COMB (@lem1352746) (@lem1352745)). Qed.
Lemma lem1352748 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1352747) (@lem1352708 h1)). Qed.
Lemma lem1352766 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1352768 (x : real) : ((term19 x) = term20) = ((term19 x) = term20).
Proof. exact (eq_refl ((term19 x) = term20)). Qed.
Lemma lem1352769 : term21 = term21.
Proof. exact (fun_ext (fun x : real => @lem1352768 x)). Qed.
Lemma lem1352770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352772 : term22 = term22.
Proof. exact (MK_COMB (@lem1352770) (@lem1352769)). Qed.
Lemma lem1352773 (h1 : term22) : term22.
Proof. exact (EQ_MP (@lem1352772) (@lem1352728 h1)). Qed.
Lemma lem1352775 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1352776 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1352775 y x)). Qed.
Lemma lem1352777 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352778 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1352777) (@lem1352776 x)). Qed.
Lemma lem1352779 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1352778 x)). Qed.
Lemma lem1352780 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1352782 : term10 = term10.
Proof. exact (MK_COMB (@lem1352780) (@lem1352779)). Qed.
Lemma lem1352783 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1352782) (@lem1352748 h1)). Qed.
Lemma lem1352787 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1352788 (_24070 : real) (h1 : term22) : term34 _24070.
Proof. exact (@lem1352773 h1 _24070). Qed.
Lemma lem1352789 (_24070 : real) : (term34 _24070) = ((term19 _24070) = term20).
Proof. exact (eq_refl (term34 _24070)). Qed.
Lemma lem1352791 (_24071 : real) (h1 : term10) : term35 _24071.
Proof. exact (@lem1352783 h1 _24071). Qed.
Lemma lem1352792 (_24071 : real) : (term35 _24071) = (term17 _24071).
Proof. exact (eq_refl (term35 _24071)). Qed.
Lemma lem1352793 (_24071 : real) (h1 : term10) : term17 _24071.
Proof. exact (EQ_MP (@lem1352792 _24071) (@lem1352791 _24071 h1)). Qed.
Lemma lem1352794 (_24071 : real) (_24072 : real) (h1 : term10) : term36 _24071 _24072.
Proof. exact (@lem1352793 _24071 h1 _24072). Qed.
Lemma lem1352795 (_24072 : real) (_24071 : real) : (term36 _24071 _24072) = ((real_add _24071 _24072) = (real_add _24072 _24071)).
Proof. exact (eq_refl (term36 _24071 _24072)). Qed.
Lemma lem1352802 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1352843 (x : real) (y : real) (z : real) : term37 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1352847 (_24072 : real) (_24071 : real) (h1 : term10) : (real_add _24071 _24072) = (real_add _24072 _24071).
Proof. exact (EQ_MP (@lem1352795 _24072 _24071) (@lem1352794 _24071 _24072 h1)). Qed.
Lemma lem1352848 (x : real) (h1 : term10) : (term19 x) = (term23 x).
Proof. exact (@lem1352847 x (real_neg x) h1). Qed.
Lemma lem1352849 (x : real) (h1 : term10) : term38 x.
Proof. exact (fun h0 : term39 x => @lem1352848 x h1). Qed.
Lemma lem1352851 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352852 (x : real) : (term38 x) = ((term19 x) = (term23 x)).
Proof. exact (@lem1352851 ((term19 x) = (term23 x))). Qed.
Lemma lem1352853 (x : real) (h1 : term10) : (term19 x) = (term23 x).
Proof. exact (EQ_MP (@lem1352852 x) (@lem1352849 x h1)). Qed.
Lemma lem1352855 (_24070 : real) (h1 : term22) : (term19 _24070) = term20.
Proof. exact (EQ_MP (@lem1352789 _24070) (@lem1352788 _24070 h1)). Qed.
Lemma lem1352856 (x : real) (h1 : term22) : (term19 x) = term20.
Proof. exact (@lem1352855 x h1). Qed.
Lemma lem1352857 (x : real) (h1 : term22) : term41 x.
Proof. exact (fun h0 : term42 x => @lem1352856 x h1). Qed.
Lemma lem1352859 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352860 (x : real) : (term41 x) = ((term19 x) = term20).
Proof. exact (@lem1352859 ((term19 x) = term20)). Qed.
Lemma lem1352861 (x : real) (h1 : term22) : (term19 x) = term20.
Proof. exact (EQ_MP (@lem1352860 x) (@lem1352857 x h1)). Qed.
Lemma lem1352879 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1352880 (y : real) (x : real) (z : real) : (term43 x y z) = (term44 y x z).
Proof. exact (@lem1352879 (y = z) (term45 x z)). Qed.
Lemma lem1352890 (x : real) (y : real) : (term46 x y) = (term46 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1352891 (y : real) (x : real) (z : real) : (term37 x y z) = (term47 y x z).
Proof. exact (MK_COMB (@lem1352890 x y) (@lem1352880 y x z)). Qed.
Lemma lem1352895 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1352896 (y : real) (x : real) (z : real) : (term47 y x z) = (term49 y x z).
Proof. exact (@lem1352895 (y = z) (term45 x y) (term45 x z)). Qed.
Lemma lem1352918 (y : real) (x : real) (z : real) : (term37 x y z) = (term49 y x z).
Proof. exact (TRANS (@lem1352891 y x z) (@lem1352896 y x z)). Qed.
Lemma lem1352919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1352920 (y : real) (x : real) (z : real) : (term50 x y z) = (term51 y x z).
Proof. exact (MK_COMB (@lem1352919) (@lem1352918 y x z)). Qed.
Lemma lem1352942 (y : real) (x : real) (z : real) : (term49 y x z) = (term49 y x z).
Proof. exact (eq_refl (term49 y x z)). Qed.
Lemma lem1352943 (y : real) (x : real) (z : real) : ((term37 x y z) = (term49 y x z)) = ((term49 y x z) = (term49 y x z)).
Proof. exact (MK_COMB (@lem1352920 y x z) (@lem1352942 y x z)). Qed.
Lemma lem1352945 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1352946 (x : Prop) : (x = x) = True.
Proof. exact (@lem1352945 Prop x). Qed.
Lemma lem1352947 (y : real) (x : real) (z : real) : ((term49 y x z) = (term49 y x z)) = True.
Proof. exact (@lem1352946 (term49 y x z)). Qed.
Lemma lem1352948 (y : real) (x : real) (z : real) : ((term37 x y z) = (term49 y x z)) = True.
Proof. exact (TRANS (@lem1352943 y x z) (@lem1352947 y x z)). Qed.
Lemma lem1352949 (y : real) (x : real) (z : real) : True = ((term37 x y z) = (term49 y x z)).
Proof. exact (SYM (@lem1352948 y x z)). Qed.
Lemma lem1352950 (y : real) (x : real) (z : real) : (term37 x y z) = (term49 y x z).
Proof. exact (EQ_MP (@lem1352949 y x z) (@lem0)). Qed.
Lemma lem1352951 (y : real) (x : real) (z : real) : term49 y x z.
Proof. exact (EQ_MP (@lem1352950 y x z) (@lem1352843 x y z)). Qed.
Lemma lem1352953 (b : Prop) (a : Prop) : (a \/ b) = (term52 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1352954 (x : real) (y : real) (z : real) : (term49 y x z) = (term53 x y z).
Proof. exact (@lem1352953 (term54 y x z) (y = z)). Qed.
Lemma lem1352956 (a : Prop) (b : Prop) : (term55 a b) = (term56 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1352957 (y : real) (x : real) (z : real) : (term57 y x z) = (term58 y x z).
Proof. exact (@lem1352956 (term45 x y) (term45 x z)). Qed.
Lemma lem1352959 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352960 (x : real) (y : real) : (term60 x y) = (x = y).
Proof. exact (@lem1352959 (x = y)). Qed.
Lemma lem1352961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1352962 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1352961) (@lem1352960 x y)). Qed.
Lemma lem1352964 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1352965 (x : real) (z : real) : (term60 x z) = (x = z).
Proof. exact (@lem1352964 (x = z)). Qed.
Lemma lem1352966 (y : real) (x : real) (z : real) : (term58 y x z) = (term63 y x z).
Proof. exact (MK_COMB (@lem1352962 x y) (@lem1352965 x z)). Qed.
Lemma lem1352967 (y : real) (x : real) (z : real) : (term57 y x z) = (term63 y x z).
Proof. exact (TRANS (@lem1352957 y x z) (@lem1352966 y x z)). Qed.
Lemma lem1352968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1352969 (y : real) (x : real) (z : real) : (term64 y x z) = (term65 y x z).
Proof. exact (MK_COMB (@lem1352968) (@lem1352967 y x z)). Qed.
Lemma lem1352970 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1352971 (x : real) (y : real) (z : real) : (term53 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1352969 y x z) (@lem1352970 y z)). Qed.
Lemma lem1352972 (x : real) (y : real) (z : real) : (term49 y x z) = (term66 x y z).
Proof. exact (TRANS (@lem1352954 x y z) (@lem1352971 x y z)). Qed.
Lemma lem1352974 (x : real) (h1 : term10) (h2 : term22) : term67 x.
Proof. exact (conj (@lem1352853 x h1) (@lem1352861 x h2)). Qed.
Lemma lem1352976 (x : real) (y : real) (z : real) : term66 x y z.
Proof. exact (EQ_MP (@lem1352972 x y z) (@lem1352951 y x z)). Qed.
Lemma lem1352977 (x : real) : term68 x.
Proof. exact (@lem1352976 (term19 x) (term23 x) term20). Qed.
Lemma lem1352980 (x : real) (h1 : term10) (h2 : term22) : (term23 x) = term20.
Proof. exact (@lem1352977 x (@lem1352974 x h1 h2)). Qed.
Lemma lem1352981 (x : real) (h1 : term10) (h2 : term22) : term69 x.
Proof. exact (fun h0 : term30 x => @lem1352980 x h1 h2). Qed.
Lemma lem1352983 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1352984 (x : real) : (term69 x) = ((term23 x) = term20).
Proof. exact (@lem1352983 ((term23 x) = term20)). Qed.
Lemma lem1352985 (x : real) (h1 : term10) (h2 : term22) : (term23 x) = term20.
Proof. exact (EQ_MP (@lem1352984 x) (@lem1352981 x h1 h2)). Qed.
Lemma lem1352988 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1352990 (x : real) : (term30 x) = (term70 x).
Proof. exact (@lem1352988 ((term23 x) = term20)). Qed.
Lemma lem1352993 (x : real) (h1 : term30 x) : term70 x.
Proof. exact (EQ_MP (@lem1352990 x) (@lem1352802 x h1)). Qed.
Lemma lem1352996 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (@lem1352993 x h3 (@lem1352985 x h1 h2)). Qed.
Lemma lem1352997 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term71.
Proof. exact (fun h0 : ~ False => @lem1352996 x h1 h2 h3). Qed.
Lemma lem1352999 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1353000 : term71 = False.
Proof. exact (@lem1352999 False). Qed.
Lemma lem1353001 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353000) (@lem1352997 x h1 h2 h3)). Qed.
Lemma lem1353002 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1353001 x h1 h2 h3) (fun h4 : False => @lem1352802 x h3)). Qed.
Lemma lem1353003 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353002 x h1 h2 h3) (@lem1352802 x h3)). Qed.
Lemma lem1353004 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1353003 x h1 h2 h3) (fun h4 : False => @lem1352787 x h3)). Qed.
Lemma lem1353005 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353004 x h1 h2 h3) (@lem1352787 x h3)). Qed.
Lemma lem1353006 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1353005 x h1 h2 h3) (fun h4 : False => @lem1352787 x h3)). Qed.
Lemma lem1353007 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353006 x h1 h2 h3) (@lem1352787 x h3)). Qed.
Lemma lem1353008 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1353007 x h1 h2 h3) (fun h4 : False => @lem1352783 h1)). Qed.
Lemma lem1353009 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353008 x h1 h2 h3) (@lem1352783 h1)). Qed.
Lemma lem1353010 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term22 = False.
Proof. exact (prop_ext (fun h4 : term22 => @lem1353009 x h1 h2 h3) (fun h4 : False => @lem1352773 h2)). Qed.
Lemma lem1353011 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353010 x h1 h2 h3) (@lem1352773 h2)). Qed.
Lemma lem1353012 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : (term30 x) = False.
Proof. exact (prop_ext (fun h4 : term30 x => @lem1353011 x h1 h2 h3) (fun h4 : False => @lem1352766 x h3)). Qed.
Lemma lem1353013 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353012 x h1 h2 h3) (@lem1352766 x h3)). Qed.
Lemma lem1353014 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1353013 x h1 h2 h3) (fun h4 : False => @lem1352748 h1)). Qed.
Lemma lem1353015 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353014 x h1 h2 h3) (@lem1352748 h1)). Qed.
Lemma lem1353016 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : term22 = False.
Proof. exact (prop_ext (fun h4 : term22 => @lem1353015 x h1 h2 h3) (fun h4 : False => @lem1352728 h2)). Qed.
Lemma lem1353017 (x : real) (h1 : term10) (h2 : term22) (h3 : term30 x) : False.
Proof. exact (EQ_MP (@lem1353016 x h1 h2 h3) (@lem1352728 h2)). Qed.
Lemma lem1353018 (h1 : term10) (h2 : term22) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1352675 h3) (fun x : real => fun h0 : term32 x => @lem1353017 x h1 h2 h0)). Qed.
Lemma lem1353019 (h1 : term10) (h2 : term22) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1353018 h1 h2 h3) (fun h4 : False => @lem1352708 h1)). Qed.
Lemma lem1353020 (h1 : term10) (h2 : term22) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1353019 h1 h2 h3) (@lem1352708 h1)). Qed.
Lemma lem1353021 (h1 : term10) (h2 : term22) (h3 : term3) : term22 = False.
Proof. exact (prop_ext (fun h4 : term22 => @lem1353020 h1 h2 h3) (fun h4 : False => @lem1352688 h2)). Qed.
Lemma lem1353022 (h1 : term10) (h2 : term22) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1353021 h1 h2 h3) (@lem1352688 h2)). Qed.
Lemma lem1353023 (h1 : term22) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1353022 h0 h1 h2). Qed.
Lemma lem1353024 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1353025 (h1 : term22) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1353024) (@lem1353023 h1 h2)). Qed.
Lemma lem1353026 (h1 : term3) : term13.
Proof. exact (fun h0 : term22 => @lem1353025 h0 h1). Qed.
Lemma lem1353027 : term15.
Proof. exact (fun h0 : term3 => @lem1353026 h0). Qed.
Lemma lem1353028 : term4.
Proof. exact (EQ_MP (@lem1352652) (@lem1353027)). Qed.
Lemma lem1353030 : term4.
Proof. exact (@lem1352560 (@lem1353028)). Qed.
Lemma lem1353031 (h1 : term3) : term12.
Proof. exact (@lem1353030 (@lem1352545 h1)). Qed.
Lemma lem1353032 (h1 : term3) : term8.
Proof. exact (@lem1353031 h1 (@lem1338588)). Qed.
Lemma lem1353033 (h1 : term3) : False.
Proof. exact (@lem1353032 h1 (@lem1338238)). Qed.
Lemma lem1353034 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1353033 h1) (fun h2 : False => @lem1352545 h1)). Qed.
Lemma lem1353035 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1353034 h1) (@lem1352545 h1)). Qed.
Lemma lem1353036 : term2.
Proof. exact (fun h0 : term3 => @lem1353035 h0). Qed.
Lemma lem1353037 : term1.
Proof. exact (EQ_MP (@lem1352544) (@lem1353036)). Qed.
