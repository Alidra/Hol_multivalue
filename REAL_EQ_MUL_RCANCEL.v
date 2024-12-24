Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_MUL_RCANCEL_term_abbrevs.
Require Import REAL_EQ_MUL_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem1586601 (x : real) : term0 x.
Proof. exact (@lem1586590 x). Qed.
Lemma lem1586602 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1586603 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1586602 x) (@lem1586601 x)). Qed.
Lemma lem1586604 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1586603 x y). Qed.
Lemma lem1586605 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1586606 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1586605 x y) (@lem1586604 x y)). Qed.
Lemma lem1586607 (x : real) (y : real) (z : real) : term4 x y z.
Proof. exact (@lem1586606 x y z). Qed.
Lemma lem1586608 (x : real) (y : real) (z : real) : (term4 x y z) = (((real_mul x y) = (real_mul x z)) = (term5 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1586610 (x : real) : term6 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1586611 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1586612 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1586611 x) (@lem1586610 x)). Qed.
Lemma lem1586613 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1586612 x y). Qed.
Lemma lem1586614 (y : real) (x : real) : (term8 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1586633 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1586614 y x) (@lem1586613 x y)). Qed.
Lemma lem1586634 (z : real) (x : real) : (real_mul x z) = (real_mul z x).
Proof. exact (@lem1586633 z x). Qed.
Lemma lem1586635 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1586636 (z : real) (x : real) : (term9 x z) = (term9 z x).
Proof. exact (MK_COMB (@lem1586635) (@lem1586634 z x)). Qed.
Lemma lem1586638 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1586614 y x) (@lem1586613 x y)). Qed.
Lemma lem1586639 (z : real) (y : real) : (real_mul y z) = (real_mul z y).
Proof. exact (@lem1586638 z y). Qed.
Lemma lem1586640 (x : real) (z : real) (y : real) : ((real_mul x z) = (real_mul y z)) = ((real_mul z x) = (real_mul z y)).
Proof. exact (MK_COMB (@lem1586636 z x) (@lem1586639 z y)). Qed.
Lemma lem1586641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1586642 (x : real) (z : real) (y : real) : (term10 x y z) = (term11 x z y).
Proof. exact (MK_COMB (@lem1586641) (@lem1586640 x z y)). Qed.
Lemma lem1586649 (x : real) (y : real) (z : real) : (term12 x y z) = (term12 x y z).
Proof. exact (eq_refl (term12 x y z)). Qed.
Lemma lem1586650 (x : real) (y : real) (z : real) : (((real_mul x z) = (real_mul y z)) = (term12 x y z)) = (((real_mul z x) = (real_mul z y)) = (term12 x y z)).
Proof. exact (MK_COMB (@lem1586642 x z y) (@lem1586649 x y z)). Qed.
Lemma lem1586651 (x : real) (y : real) : (term13 x y) = (term14 x y).
Proof. exact (fun_ext (fun z : real => @lem1586650 x y z)). Qed.
Lemma lem1586652 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586653 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem1586652) (@lem1586651 x y)). Qed.
Lemma lem1586654 (x : real) : (term17 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1586653 x y)). Qed.
Lemma lem1586655 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586656 (x : real) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1586655) (@lem1586654 x)). Qed.
Lemma lem1586657 : term21 = term22.
Proof. exact (fun_ext (fun x : real => @lem1586656 x)). Qed.
Lemma lem1586658 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586659 : term23 = term24.
Proof. exact (MK_COMB (@lem1586658) (@lem1586657)). Qed.
Lemma lem1586660 : term24 = term23.
Proof. exact (SYM (@lem1586659)). Qed.
Lemma lem1586676 (x : real) (y : real) (z : real) : ((real_mul x y) = (real_mul x z)) = (term5 x y z).
Proof. exact (EQ_MP (@lem1586608 x y z) (@lem1586607 x y z)). Qed.
Lemma lem1586677 (z : real) (x : real) (y : real) : ((real_mul z x) = (real_mul z y)) = (term5 z x y).
Proof. exact (@lem1586676 z x y). Qed.
Lemma lem1586684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1586685 (z : real) (x : real) (y : real) : (term11 x z y) = (term25 z x y).
Proof. exact (MK_COMB (@lem1586684) (@lem1586677 z x y)). Qed.
Lemma lem1586692 (x : real) (y : real) (z : real) : (term12 x y z) = (term12 x y z).
Proof. exact (eq_refl (term12 x y z)). Qed.
Lemma lem1586693 (x : real) (y : real) (z : real) : (((real_mul z x) = (real_mul z y)) = (term12 x y z)) = ((term5 z x y) = (term12 x y z)).
Proof. exact (MK_COMB (@lem1586685 z x y) (@lem1586692 x y z)). Qed.
Lemma lem1586696 (x : real) (y : real) : (term14 x y) = (term26 x y).
Proof. exact (fun_ext (fun z : real => @lem1586693 x y z)). Qed.
Lemma lem1586697 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586698 (x : real) (y : real) : (term16 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1586697) (@lem1586696 x y)). Qed.
Lemma lem1586703 (x : real) : (term18 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1586698 x y)). Qed.
Lemma lem1586704 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586705 (x : real) : (term20 x) = (term29 x).
Proof. exact (MK_COMB (@lem1586704) (@lem1586703 x)). Qed.
Lemma lem1586710 : term22 = term30.
Proof. exact (fun_ext (fun x : real => @lem1586705 x)). Qed.
Lemma lem1586711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586712 : term24 = term31.
Proof. exact (MK_COMB (@lem1586711) (@lem1586710)). Qed.
Lemma lem1586717 : term31 = term24.
Proof. exact (SYM (@lem1586712)). Qed.
Lemma lem1586719 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1586720 : term31 = term33.
Proof. exact (@lem1586719 term31). Qed.
Lemma lem1586721 : term33 = term31.
Proof. exact (SYM (@lem1586720)). Qed.
Lemma lem1586722 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1586725 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1586726 : term35.
Proof. exact (fun h0 : term33 => @lem1586725 h0). Qed.
Lemma lem1586727 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1586728 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1586729 (h1 : term33) (h2 : term35) : term33.
Proof. exact (@lem1586727 h2 (@lem1586728 h1)). Qed.
Lemma lem1586730 (h1 : term33) : term36.
Proof. exact (fun h0 : term35 => @lem1586729 h1 h0). Qed.
Lemma lem1586731 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem1586732 (h1 : term33) (h2 : term35) : term33.
Proof. exact (@lem1586730 h1 (@lem1586731 h2)). Qed.
Lemma lem1586733 (h1 : term35) : term35.
Proof. exact (fun h0 : term33 => @lem1586732 h0 h1). Qed.
Lemma lem1586734 : term37.
Proof. exact (fun h0 : term35 => @lem1586733 h0). Qed.
Lemma lem1586737 : term35.
Proof. exact (@lem1586734 (@lem1586726)). Qed.
Lemma lem1586739 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1586740 : term33 = term38.
Proof. exact (@lem1586739 term34). Qed.
Lemma lem1586742 (t : Prop) : (term39 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1586743 : term38 = term31.
Proof. exact (@lem1586742 term31). Qed.
Lemma lem1586764 : term33 = term31.
Proof. exact (TRANS (@lem1586740) (@lem1586743)). Qed.
Lemma lem1586777 (x : real) (y : real) (z : real) : ((term5 z x y) = (term12 x y z)) = ((term5 z x y) = (term12 x y z)).
Proof. exact (eq_refl ((term5 z x y) = (term12 x y z))). Qed.
Lemma lem1586778 (x : real) (y : real) : (term26 x y) = (term26 x y).
Proof. exact (fun_ext (fun z : real => @lem1586777 x y z)). Qed.
Lemma lem1586779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586780 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1586779) (@lem1586778 x y)). Qed.
Lemma lem1586781 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1586780 x y)). Qed.
Lemma lem1586782 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586783 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1586782) (@lem1586781 x)). Qed.
Lemma lem1586784 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1586783 x)). Qed.
Lemma lem1586785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1586786 : term31 = term31.
Proof. exact (MK_COMB (@lem1586785) (@lem1586784)). Qed.
Lemma lem1586811 : term33 = term31.
Proof. exact (TRANS (@lem1586764) (@lem1586786)). Qed.
Lemma lem1586812 : term31 = term33.
Proof. exact (SYM (@lem1586811)). Qed.
Lemma lem1586814 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1586815 (x : real) (y : real) (z : real) : ((term5 z x y) = (term12 x y z)) = (term40 x y z).
Proof. exact (@lem1586814 ((term5 z x y) = (term12 x y z))). Qed.
Lemma lem1586816 (x : real) (y : real) (z : real) : (term40 x y z) = ((term5 z x y) = (term12 x y z)).
Proof. exact (SYM (@lem1586815 x y z)). Qed.
Lemma lem1586817 (x : real) (y : real) (z : real) (h1 : term41 x y z) : term41 x y z.
Proof. exact (h1). Qed.
Lemma lem1586826 (z : real) (x : real) (y : real) : (term42 z x y) = (term43 z x y).
Proof. exact (@lem17160 (z = term44) (x = y)). Qed.
Lemma lem1586838 (x : real) (y : real) (z : real) : (term45 x y z) = (term46 x y z).
Proof. exact (@lem17160 (x = y) (z = term44)). Qed.
Lemma lem1586841 (x : real) (y : real) (z : real) : (term12 x y z) = (term12 x y z).
Proof. exact (eq_refl (term12 x y z)). Qed.
Lemma lem1586842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1586843 (z : real) (x : real) (y : real) : (term47 z x y) = (term48 z x y).
Proof. exact (MK_COMB (@lem1586842) (@lem1586826 z x y)). Qed.
Lemma lem1586844 (x : real) (y : real) (z : real) : (term49 x y z) = (term50 x y z).
Proof. exact (MK_COMB (@lem1586843 z x y) (@lem1586841 x y z)). Qed.
Lemma lem1586846 (z : real) (x : real) (y : real) : (term51 z x y) = (term51 z x y).
Proof. exact (eq_refl (term51 z x y)). Qed.
Lemma lem1586847 (x : real) (y : real) (z : real) : (term52 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1586846 z x y) (@lem1586838 x y z)). Qed.
Lemma lem1586848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1586849 (x : real) (y : real) (z : real) : (term54 x y z) = (term55 x y z).
Proof. exact (MK_COMB (@lem1586848) (@lem1586847 x y z)). Qed.
Lemma lem1586850 (x : real) (y : real) (z : real) : (term56 x y z) = (term57 x y z).
Proof. exact (MK_COMB (@lem1586849 x y z) (@lem1586844 x y z)). Qed.
Lemma lem1586851 (x : real) (y : real) (z : real) : (term41 x y z) = (term56 x y z).
Proof. exact (@lem17646 (term5 z x y) (term12 x y z)). Qed.
Lemma lem1586856 (x : real) (y : real) (z : real) : (term41 x y z) = (term57 x y z).
Proof. exact (TRANS (@lem1586851 x y z) (@lem1586850 x y z)). Qed.
Lemma lem1586943 (x : real) (y : real) (z : real) (h1 : term41 x y z) : term57 x y z.
Proof. exact (EQ_MP (@lem1586856 x y z) (@lem1586817 x y z h1)). Qed.
Lemma lem1586944 (x : real) (y : real) (z : real) (h1 : term53 x y z) : term53 x y z.
Proof. exact (h1). Qed.
Lemma lem1586945 (x : real) (y : real) (z : real) (h1 : term50 x y z) : term50 x y z.
Proof. exact (h1). Qed.
Lemma lem1586946 (x : real) (y : real) (z : real) (h1 : term53 x y z) : term46 x y z.
Proof. exact (proj2 (@lem1586944 x y z h1)). Qed.
Lemma lem1586947 (x : real) (y : real) (z : real) (h1 : term53 x y z) : term5 z x y.
Proof. exact (proj1 (@lem1586944 x y z h1)). Qed.
Lemma lem1586952 (x : real) (y : real) (z : real) (h1 : term50 x y z) : term12 x y z.
Proof. exact (proj2 (@lem1586945 x y z h1)). Qed.
Lemma lem1586953 (x : real) (y : real) (z : real) (h1 : term50 x y z) : term43 z x y.
Proof. exact (proj1 (@lem1586945 x y z h1)). Qed.
Lemma lem1586969 (z : real) (h1 : z = term44) : z = term44.
Proof. exact (h1). Qed.
Lemma lem1586981 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1586993 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1587005 (z : real) (h1 : z = term44) : z = term44.
Proof. exact (h1). Qed.
Lemma lem1587009 (x : real) (y : real) (z : real) (h1 : term53 x y z) : term58 z.
Proof. exact (proj2 (@lem1586946 x y z h1)). Qed.
Lemma lem1587011 (z : real) (h1 : z = term44) : z = term44.
Proof. exact (h1). Qed.
Lemma lem1587013 (x : real) (y : real) (z : real) (h1 : term53 x y z) : term59 x y.
Proof. exact (proj1 (@lem1586946 x y z h1)). Qed.
Lemma lem1587017 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1587021 (x : real) (y : real) (z : real) (h1 : term50 x y z) : term59 x y.
Proof. exact (proj2 (@lem1586953 x y z h1)). Qed.
Lemma lem1587023 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1587025 (x : real) (y : real) (z : real) (h1 : term50 x y z) : term58 z.
Proof. exact (proj1 (@lem1586953 x y z h1)). Qed.
Lemma lem1587029 (z : real) (h1 : z = term44) : z = term44.
Proof. exact (h1). Qed.
Lemma lem1587058 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1587059 (z : real) (h1 : z = term44) : (term61 z) = term62.
Proof. exact (MK_COMB (@lem1587058) (@lem1587011 z h1)). Qed.
Lemma lem1587060 : term62 = term63.
Proof. exact (eq_refl term62). Qed.
Lemma lem1587061 (z : real) : (term64 z) = (term64 z).
Proof. exact (eq_refl (term64 z)). Qed.
Lemma lem1587062 (z : real) : ((term61 z) = term62) = ((term61 z) = term63).
Proof. exact (MK_COMB (@lem1587061 z) (@lem1587060)). Qed.
Lemma lem1587063 (z : real) : (term61 z) = (term58 z).
Proof. exact (eq_refl (term61 z)). Qed.
Lemma lem1587064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1587065 (z : real) : (term64 z) = (term65 z).
Proof. exact (MK_COMB (@lem1587064) (@lem1587063 z)). Qed.
Lemma lem1587066 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem1587067 (z : real) : ((term61 z) = term63) = ((term58 z) = term63).
Proof. exact (MK_COMB (@lem1587065 z) (@lem1587066)). Qed.
Lemma lem1587068 (z : real) : ((term61 z) = term62) = ((term58 z) = term63).
Proof. exact (TRANS (@lem1587062 z) (@lem1587067 z)). Qed.
Lemma lem1587069 (z : real) (h1 : z = term44) : (term58 z) = term63.
Proof. exact (EQ_MP (@lem1587068 z) (@lem1587059 z h1)). Qed.
Lemma lem1587070 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : term63.
Proof. exact (EQ_MP (@lem1587069 z h2) (@lem1587009 x y z h1)). Qed.
Lemma lem1587085 (y : real) : (term66 y) = (term66 y).
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem1587086 (x : real) (y : real) (h1 : x = y) : (term67 y x) = (term68 y).
Proof. exact (MK_COMB (@lem1587085 y) (@lem1587017 x y h1)). Qed.
Lemma lem1587087 (y : real) : (term68 y) = (term69 y).
Proof. exact (eq_refl (term68 y)). Qed.
Lemma lem1587088 (y : real) (x : real) : (term70 y x) = (term70 y x).
Proof. exact (eq_refl (term70 y x)). Qed.
Lemma lem1587089 (x : real) (y : real) : ((term67 y x) = (term68 y)) = ((term67 y x) = (term69 y)).
Proof. exact (MK_COMB (@lem1587088 y x) (@lem1587087 y)). Qed.
Lemma lem1587090 (x : real) (y : real) : (term67 y x) = (term59 x y).
Proof. exact (eq_refl (term67 y x)). Qed.
Lemma lem1587091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1587092 (x : real) (y : real) : (term70 y x) = (term71 x y).
Proof. exact (MK_COMB (@lem1587091) (@lem1587090 x y)). Qed.
Lemma lem1587093 (y : real) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem1587094 (x : real) (y : real) : ((term67 y x) = (term69 y)) = ((term59 x y) = (term69 y)).
Proof. exact (MK_COMB (@lem1587092 x y) (@lem1587093 y)). Qed.
Lemma lem1587095 (x : real) (y : real) : ((term67 y x) = (term68 y)) = ((term59 x y) = (term69 y)).
Proof. exact (TRANS (@lem1587089 x y) (@lem1587094 x y)). Qed.
Lemma lem1587096 (x : real) (y : real) (h1 : x = y) : (term59 x y) = (term69 y).
Proof. exact (EQ_MP (@lem1587095 x y) (@lem1587086 x y h1)). Qed.
Lemma lem1587097 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : term69 y.
Proof. exact (EQ_MP (@lem1587096 x y h2) (@lem1587013 x y z h1)). Qed.
Lemma lem1587140 (y : real) : (term66 y) = (term66 y).
Proof. exact (eq_refl (term66 y)). Qed.
Lemma lem1587141 (x : real) (y : real) (h1 : x = y) : (term67 y x) = (term68 y).
Proof. exact (MK_COMB (@lem1587140 y) (@lem1587023 x y h1)). Qed.
Lemma lem1587142 (y : real) : (term68 y) = (term69 y).
Proof. exact (eq_refl (term68 y)). Qed.
Lemma lem1587143 (y : real) (x : real) : (term70 y x) = (term70 y x).
Proof. exact (eq_refl (term70 y x)). Qed.
Lemma lem1587144 (x : real) (y : real) : ((term67 y x) = (term68 y)) = ((term67 y x) = (term69 y)).
Proof. exact (MK_COMB (@lem1587143 y x) (@lem1587142 y)). Qed.
Lemma lem1587145 (x : real) (y : real) : (term67 y x) = (term59 x y).
Proof. exact (eq_refl (term67 y x)). Qed.
Lemma lem1587146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1587147 (x : real) (y : real) : (term70 y x) = (term71 x y).
Proof. exact (MK_COMB (@lem1587146) (@lem1587145 x y)). Qed.
Lemma lem1587148 (y : real) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem1587149 (x : real) (y : real) : ((term67 y x) = (term69 y)) = ((term59 x y) = (term69 y)).
Proof. exact (MK_COMB (@lem1587147 x y) (@lem1587148 y)). Qed.
Lemma lem1587150 (x : real) (y : real) : ((term67 y x) = (term68 y)) = ((term59 x y) = (term69 y)).
Proof. exact (TRANS (@lem1587144 x y) (@lem1587149 x y)). Qed.
Lemma lem1587151 (x : real) (y : real) (h1 : x = y) : (term59 x y) = (term69 y).
Proof. exact (EQ_MP (@lem1587150 x y) (@lem1587141 x y h1)). Qed.
Lemma lem1587152 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : term69 y.
Proof. exact (EQ_MP (@lem1587151 x y h2) (@lem1587021 x y z h1)). Qed.
Lemma lem1587167 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1587168 (z : real) (h1 : z = term44) : (term61 z) = term62.
Proof. exact (MK_COMB (@lem1587167) (@lem1587029 z h1)). Qed.
Lemma lem1587169 : term62 = term63.
Proof. exact (eq_refl term62). Qed.
Lemma lem1587170 (z : real) : (term64 z) = (term64 z).
Proof. exact (eq_refl (term64 z)). Qed.
Lemma lem1587171 (z : real) : ((term61 z) = term62) = ((term61 z) = term63).
Proof. exact (MK_COMB (@lem1587170 z) (@lem1587169)). Qed.
Lemma lem1587172 (z : real) : (term61 z) = (term58 z).
Proof. exact (eq_refl (term61 z)). Qed.
Lemma lem1587173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1587174 (z : real) : (term64 z) = (term65 z).
Proof. exact (MK_COMB (@lem1587173) (@lem1587172 z)). Qed.
Lemma lem1587175 : term63 = term63.
Proof. exact (eq_refl term63). Qed.
Lemma lem1587176 (z : real) : ((term61 z) = term63) = ((term58 z) = term63).
Proof. exact (MK_COMB (@lem1587174 z) (@lem1587175)). Qed.
Lemma lem1587177 (z : real) : ((term61 z) = term62) = ((term58 z) = term63).
Proof. exact (TRANS (@lem1587171 z) (@lem1587176 z)). Qed.
Lemma lem1587178 (z : real) (h1 : z = term44) : (term58 z) = term63.
Proof. exact (EQ_MP (@lem1587177 z) (@lem1587168 z h1)). Qed.
Lemma lem1587179 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : term63.
Proof. exact (EQ_MP (@lem1587178 z h2) (@lem1587025 x y z h1)). Qed.
Lemma lem1587215 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1587216 : term44 = term44.
Proof. exact (@lem1587215 term44). Qed.
Lemma lem1587217 : term72.
Proof. exact (fun h0 : term63 => @lem1587216). Qed.
Lemma lem1587219 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587220 : term72 = (term44 = term44).
Proof. exact (@lem1587219 (term44 = term44)). Qed.
Lemma lem1587221 : term44 = term44.
Proof. exact (EQ_MP (@lem1587220) (@lem1587217)). Qed.
Lemma lem1587224 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1587226 : term63 = term74.
Proof. exact (@lem1587224 (term44 = term44)). Qed.
Lemma lem1587229 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : term74.
Proof. exact (EQ_MP (@lem1587226) (@lem1587070 x y z h1 h2)). Qed.
Lemma lem1587232 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : False.
Proof. exact (@lem1587229 x y z h1 h2 (@lem1587221)). Qed.
Lemma lem1587233 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : term75.
Proof. exact (fun h0 : ~ False => @lem1587232 x y z h1 h2). Qed.
Lemma lem1587235 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587236 : term75 = False.
Proof. exact (@lem1587235 False). Qed.
Lemma lem1587259 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1587260 (y : real) : y = y.
Proof. exact (@lem1587259 y). Qed.
Lemma lem1587261 (y : real) : term76 y.
Proof. exact (fun h0 : term69 y => @lem1587260 y). Qed.
Lemma lem1587263 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587264 (y : real) : (term76 y) = (y = y).
Proof. exact (@lem1587263 (y = y)). Qed.
Lemma lem1587265 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1587264 y) (@lem1587261 y)). Qed.
Lemma lem1587268 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1587270 (y : real) : (term69 y) = (term77 y).
Proof. exact (@lem1587268 (y = y)). Qed.
Lemma lem1587273 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : term77 y.
Proof. exact (EQ_MP (@lem1587270 y) (@lem1587097 z x y h1 h2)). Qed.
Lemma lem1587276 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : False.
Proof. exact (@lem1587273 z x y h1 h2 (@lem1587265 y)). Qed.
Lemma lem1587277 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : term75.
Proof. exact (fun h0 : ~ False => @lem1587276 z x y h1 h2). Qed.
Lemma lem1587279 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587280 : term75 = False.
Proof. exact (@lem1587279 False). Qed.
Lemma lem1587303 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1587304 (y : real) : y = y.
Proof. exact (@lem1587303 y). Qed.
Lemma lem1587305 (y : real) : term76 y.
Proof. exact (fun h0 : term69 y => @lem1587304 y). Qed.
Lemma lem1587307 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587308 (y : real) : (term76 y) = (y = y).
Proof. exact (@lem1587307 (y = y)). Qed.
Lemma lem1587309 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1587308 y) (@lem1587305 y)). Qed.
Lemma lem1587312 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1587314 (y : real) : (term69 y) = (term77 y).
Proof. exact (@lem1587312 (y = y)). Qed.
Lemma lem1587317 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : term77 y.
Proof. exact (EQ_MP (@lem1587314 y) (@lem1587152 z x y h1 h2)). Qed.
Lemma lem1587320 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : False.
Proof. exact (@lem1587317 z x y h1 h2 (@lem1587309 y)). Qed.
Lemma lem1587321 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : term75.
Proof. exact (fun h0 : ~ False => @lem1587320 z x y h1 h2). Qed.
Lemma lem1587323 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587324 : term75 = False.
Proof. exact (@lem1587323 False). Qed.
Lemma lem1587347 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1587348 : term44 = term44.
Proof. exact (@lem1587347 term44). Qed.
Lemma lem1587349 : term72.
Proof. exact (fun h0 : term63 => @lem1587348). Qed.
Lemma lem1587351 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587352 : term72 = (term44 = term44).
Proof. exact (@lem1587351 (term44 = term44)). Qed.
Lemma lem1587353 : term44 = term44.
Proof. exact (EQ_MP (@lem1587352) (@lem1587349)). Qed.
Lemma lem1587356 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1587358 : term63 = term74.
Proof. exact (@lem1587356 (term44 = term44)). Qed.
Lemma lem1587361 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : term74.
Proof. exact (EQ_MP (@lem1587358) (@lem1587179 x y z h1 h2)). Qed.
Lemma lem1587364 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : False.
Proof. exact (@lem1587361 x y z h1 h2 (@lem1587353)). Qed.
Lemma lem1587365 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : term75.
Proof. exact (fun h0 : ~ False => @lem1587364 x y z h1 h2). Qed.
Lemma lem1587367 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1587368 : term75 = False.
Proof. exact (@lem1587367 False). Qed.
Lemma lem1587370 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587368) (@lem1587365 x y z h1 h2)). Qed.
Lemma lem1587371 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587324) (@lem1587321 z x y h1 h2)). Qed.
Lemma lem1587372 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587280) (@lem1587277 z x y h1 h2)). Qed.
Lemma lem1587373 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587236) (@lem1587233 x y z h1 h2)). Qed.
Lemma lem1587374 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : (z = term44) = False.
Proof. exact (prop_ext (fun h3 : z = term44 => @lem1587370 x y z h1 h2) (fun h3 : False => @lem1587029 z h2)). Qed.
Lemma lem1587375 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587374 x y z h1 h2) (@lem1587029 z h2)). Qed.
Lemma lem1587376 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1587371 z x y h1 h2) (fun h3 : False => @lem1587023 x y h2)). Qed.
Lemma lem1587377 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587376 z x y h1 h2) (@lem1587023 x y h2)). Qed.
Lemma lem1587378 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1587372 z x y h1 h2) (fun h3 : False => @lem1587017 x y h2)). Qed.
Lemma lem1587379 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587378 z x y h1 h2) (@lem1587017 x y h2)). Qed.
Lemma lem1587380 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : (z = term44) = False.
Proof. exact (prop_ext (fun h3 : z = term44 => @lem1587373 x y z h1 h2) (fun h3 : False => @lem1587011 z h2)). Qed.
Lemma lem1587381 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587380 x y z h1 h2) (@lem1587011 z h2)). Qed.
Lemma lem1587382 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : (z = term44) = False.
Proof. exact (prop_ext (fun h3 : z = term44 => @lem1587375 x y z h1 h2) (fun h3 : False => @lem1587005 z h2)). Qed.
Lemma lem1587383 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587382 x y z h1 h2) (@lem1587005 z h2)). Qed.
Lemma lem1587384 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1587377 z x y h1 h2) (fun h3 : False => @lem1586993 x y h2)). Qed.
Lemma lem1587385 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587384 z x y h1 h2) (@lem1586993 x y h2)). Qed.
Lemma lem1587386 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1587379 z x y h1 h2) (fun h3 : False => @lem1586981 x y h2)). Qed.
Lemma lem1587387 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587386 z x y h1 h2) (@lem1586981 x y h2)). Qed.
Lemma lem1587388 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : (z = term44) = False.
Proof. exact (prop_ext (fun h3 : z = term44 => @lem1587381 x y z h1 h2) (fun h3 : False => @lem1586969 z h2)). Qed.
Lemma lem1587389 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587388 x y z h1 h2) (@lem1586969 z h2)). Qed.
Lemma lem1587390 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : (z = term44) = False.
Proof. exact (prop_ext (fun h3 : z = term44 => @lem1587383 x y z h1 h2) (fun h3 : False => @lem1587005 z h2)). Qed.
Lemma lem1587391 (x : real) (y : real) (z : real) (h1 : term50 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587390 x y z h1 h2) (@lem1587005 z h2)). Qed.
Lemma lem1587392 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1587385 z x y h1 h2) (fun h3 : False => @lem1586993 x y h2)). Qed.
Lemma lem1587393 (z : real) (x : real) (y : real) (h1 : term50 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587392 z x y h1 h2) (@lem1586993 x y h2)). Qed.
Lemma lem1587394 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1587387 z x y h1 h2) (fun h3 : False => @lem1586981 x y h2)). Qed.
Lemma lem1587395 (z : real) (x : real) (y : real) (h1 : term53 x y z) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1587394 z x y h1 h2) (@lem1586981 x y h2)). Qed.
Lemma lem1587396 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : (z = term44) = False.
Proof. exact (prop_ext (fun h3 : z = term44 => @lem1587389 x y z h1 h2) (fun h3 : False => @lem1586969 z h2)). Qed.
Lemma lem1587397 (x : real) (y : real) (z : real) (h1 : term53 x y z) (h2 : z = term44) : False.
Proof. exact (EQ_MP (@lem1587396 x y z h1 h2) (@lem1586969 z h2)). Qed.
Lemma lem1587398 (x : real) (y : real) (z : real) (h1 : term50 x y z) : False.
Proof. exact (or_elim (@lem1586952 x y z h1) (fun h0 : x = y => @lem1587393 z x y h1 h0) (fun h0 : z = term44 => @lem1587391 x y z h1 h0)). Qed.
Lemma lem1587399 (x : real) (y : real) (z : real) (h1 : term53 x y z) : False.
Proof. exact (or_elim (@lem1586947 x y z h1) (fun h0 : z = term44 => @lem1587397 x y z h1 h0) (fun h0 : x = y => @lem1587395 z x y h1 h0)). Qed.
Lemma lem1587400 (x : real) (y : real) (z : real) (h1 : term41 x y z) : False.
Proof. exact (or_elim (@lem1586943 x y z h1) (fun h0 : term53 x y z => @lem1587399 x y z h0) (fun h0 : term50 x y z => @lem1587398 x y z h0)). Qed.
Lemma lem1587401 (x : real) (y : real) (z : real) (h1 : term41 x y z) : (term41 x y z) = False.
Proof. exact (prop_ext (fun h2 : term41 x y z => @lem1587400 x y z h1) (fun h2 : False => @lem1586817 x y z h1)). Qed.
Lemma lem1587402 (x : real) (y : real) (z : real) (h1 : term41 x y z) : False.
Proof. exact (EQ_MP (@lem1587401 x y z h1) (@lem1586817 x y z h1)). Qed.
Lemma lem1587403 (x : real) (y : real) (z : real) : term40 x y z.
Proof. exact (fun h0 : term41 x y z => @lem1587402 x y z h0). Qed.
Lemma lem1587404 (x : real) (y : real) (z : real) : (term5 z x y) = (term12 x y z).
Proof. exact (EQ_MP (@lem1586816 x y z) (@lem1587403 x y z)). Qed.
Lemma lem1587409 (x : real) (y : real) : term27 x y.
Proof. exact (fun z : real => @lem1587404 x y z). Qed.
Lemma lem1587414 (x : real) : term29 x.
Proof. exact (fun y : real => @lem1587409 x y). Qed.
Lemma lem1587419 : term31.
Proof. exact (fun x : real => @lem1587414 x). Qed.
Lemma lem1587420 : term33.
Proof. exact (EQ_MP (@lem1586812) (@lem1587419)). Qed.
Lemma lem1587422 : term33.
Proof. exact (@lem1586737 (@lem1587420)). Qed.
Lemma lem1587423 (h1 : term34) : False.
Proof. exact (@lem1587422 (@lem1586722 h1)). Qed.
Lemma lem1587424 (h1 : term34) : term34 = False.
Proof. exact (prop_ext (fun h2 : term34 => @lem1587423 h1) (fun h2 : False => @lem1586722 h1)). Qed.
Lemma lem1587425 (h1 : term34) : False.
Proof. exact (EQ_MP (@lem1587424 h1) (@lem1586722 h1)). Qed.
Lemma lem1587426 : term33.
Proof. exact (fun h0 : term34 => @lem1587425 h0). Qed.
Lemma lem1587427 : term31.
Proof. exact (EQ_MP (@lem1586721) (@lem1587426)). Qed.
Lemma lem1587428 : term24.
Proof. exact (EQ_MP (@lem1586717) (@lem1587427)). Qed.
Lemma lem1587429 : term23.
Proof. exact (EQ_MP (@lem1586660) (@lem1587428)). Qed.
