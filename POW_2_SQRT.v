Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POW_2_SQRT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SQRT_UNIQUE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
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
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem1900061 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1900062 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1900063 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1900062 t1) (@lem1900061 t1)). Qed.
Lemma lem1900064 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1900063 t1 t2). Qed.
Lemma lem1900065 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1900066 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1900065 t1 t2) (@lem1900064 t1 t2)). Qed.
Lemma lem1900067 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1900066 t1 t2 t3). Qed.
Lemma lem1900068 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1900069 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1900068 t1 t2 t3) (@lem1900067 t1 t2 t3)). Qed.
Lemma lem1900070 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1900069 t1 t2 t3)). Qed.
Lemma lem1900072 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1900073 : term8 = term9.
Proof. exact (@lem1900072 term8). Qed.
Lemma lem1900074 : term9 = term8.
Proof. exact (SYM (@lem1900073)). Qed.
Lemma lem1900075 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1900078 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1900079 : term12.
Proof. exact (fun h0 : term11 => @lem1900078 h0). Qed.
Lemma lem1900080 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1900081 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1900082 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1900080 h2 (@lem1900081 h1)). Qed.
Lemma lem1900083 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1900082 h1 h0). Qed.
Lemma lem1900084 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1900085 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1900083 h1 (@lem1900084 h2)). Qed.
Lemma lem1900086 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1900085 h0 h1). Qed.
Lemma lem1900087 : term14.
Proof. exact (fun h0 : term12 => @lem1900086 h0). Qed.
Lemma lem1900090 : term12.
Proof. exact (@lem1900087 (@lem1900079)). Qed.
Lemma lem1900100 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1900101 : term15 = term16.
Proof. exact (@lem1900100 term17). Qed.
Lemma lem1900114 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1900121 : term11 = term19.
Proof. exact (MK_COMB (@lem1900114) (@lem1900101)). Qed.
Lemma lem1900130 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1900131 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1900130 x y)). Qed.
Lemma lem1900132 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900133 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1900132) (@lem1900131 x)). Qed.
Lemma lem1900134 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1900133 x)). Qed.
Lemma lem1900135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900136 : term17 = term17.
Proof. exact (MK_COMB (@lem1900135) (@lem1900134)). Qed.
Lemma lem1900137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1900138 : term16 = term16.
Proof. exact (MK_COMB (@lem1900137) (@lem1900136)). Qed.
Lemma lem1900143 (x : real) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1900144 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1900143 x)). Qed.
Lemma lem1900145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900146 : term8 = term8.
Proof. exact (MK_COMB (@lem1900145) (@lem1900144)). Qed.
Lemma lem1900147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1900148 : term10 = term10.
Proof. exact (MK_COMB (@lem1900147) (@lem1900146)). Qed.
Lemma lem1900149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1900150 : term18 = term18.
Proof. exact (MK_COMB (@lem1900149) (@lem1900148)). Qed.
Lemma lem1900151 : term19 = term19.
Proof. exact (MK_COMB (@lem1900150) (@lem1900138)). Qed.
Lemma lem1900180 : term11 = term19.
Proof. exact (TRANS (@lem1900121) (@lem1900151)). Qed.
Lemma lem1900181 : term19 = term11.
Proof. exact (SYM (@lem1900180)). Qed.
Lemma lem1900182 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1900183 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1900190 (x : real) : (term26 x) = (term27 x).
Proof. exact (@lem17362 (term28 x) ((term29 x) = x)). Qed.
Lemma lem1900191 (P : real -> Prop) : (term30 P) = (term31 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1900192 : term10 = term32.
Proof. exact (@lem1900191 term25). Qed.
Lemma lem1900193 (x : real) : (term33 x) = (term24 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1900194 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1900195 (x : real) : (term34 x) = (term26 x).
Proof. exact (MK_COMB (@lem1900194) (@lem1900193 x)). Qed.
Lemma lem1900196 (x : real) : (term34 x) = (term27 x).
Proof. exact (TRANS (@lem1900195 x) (@lem1900190 x)). Qed.
Lemma lem1900197 : term35 = term36.
Proof. exact (fun_ext (fun x : real => @lem1900196 x)). Qed.
Lemma lem1900198 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1900199 : term32 = term37.
Proof. exact (MK_COMB (@lem1900198) (@lem1900197)). Qed.
Lemma lem1900252 : term10 = term37.
Proof. exact (TRANS (@lem1900192) (@lem1900199)). Qed.
Lemma lem1900253 (h1 : term10) : term37.
Proof. exact (EQ_MP (@lem1900252) (@lem1900182 h1)). Qed.
Lemma lem1900260 (y : real) (x : real) : (term38 y x) = (term39 y x).
Proof. exact (@lem17045 (term28 y) ((term40 y) = x)). Qed.
Lemma lem1900261 (x : real) (y : real) : ((sqrt x) = y) = ((sqrt x) = y).
Proof. exact (eq_refl ((sqrt x) = y)). Qed.
Lemma lem1900262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1900263 (y : real) (x : real) : (term41 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1900262) (@lem1900260 y x)). Qed.
Lemma lem1900264 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1900263 y x) (@lem1900261 x y)). Qed.
Lemma lem1900265 (x : real) (y : real) : (term20 x y) = (term43 x y).
Proof. exact (@lem17265 (term45 y x) ((sqrt x) = y)). Qed.
Lemma lem1900266 (x : real) (y : real) : (term20 x y) = (term44 x y).
Proof. exact (TRANS (@lem1900265 x y) (@lem1900264 x y)). Qed.
Lemma lem1900267 (x : real) : (term21 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1900266 x y)). Qed.
Lemma lem1900268 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900269 (x : real) : (term22 x) = (term47 x).
Proof. exact (MK_COMB (@lem1900268) (@lem1900267 x)). Qed.
Lemma lem1900270 : term23 = term48.
Proof. exact (fun_ext (fun x : real => @lem1900269 x)). Qed.
Lemma lem1900271 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900328 : term17 = term49.
Proof. exact (MK_COMB (@lem1900271) (@lem1900270)). Qed.
Lemma lem1900329 (h1 : term17) : term49.
Proof. exact (EQ_MP (@lem1900328) (@lem1900183 h1)). Qed.
Lemma lem1900371 (x : real) (y : real) : (term44 x y) = (term44 x y).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1900372 (x : real) : (term46 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1900371 x y)). Qed.
Lemma lem1900373 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900374 (x : real) : (term47 x) = (term47 x).
Proof. exact (MK_COMB (@lem1900373) (@lem1900372 x)). Qed.
Lemma lem1900375 : term48 = term48.
Proof. exact (fun_ext (fun x : real => @lem1900374 x)). Qed.
Lemma lem1900376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900377 : term49 = term49.
Proof. exact (MK_COMB (@lem1900376) (@lem1900375)). Qed.
Lemma lem1900378 (h1 : term17) : term49.
Proof. exact (EQ_MP (@lem1900377) (@lem1900329 h1)). Qed.
Lemma lem1900410 (x : real) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1900426 (x : real) (y : real) : (term44 x y) = (term44 x y).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem1900427 (x : real) : (term46 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1900426 x y)). Qed.
Lemma lem1900428 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900429 (x : real) : (term47 x) = (term47 x).
Proof. exact (MK_COMB (@lem1900428) (@lem1900427 x)). Qed.
Lemma lem1900430 : term48 = term48.
Proof. exact (fun_ext (fun x : real => @lem1900429 x)). Qed.
Lemma lem1900431 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900433 : term49 = term49.
Proof. exact (MK_COMB (@lem1900431) (@lem1900430)). Qed.
Lemma lem1900434 (h1 : term17) : term49.
Proof. exact (EQ_MP (@lem1900433) (@lem1900378 h1)). Qed.
Lemma lem1900443 (_27029 : real) (h1 : term17) : term50 _27029.
Proof. exact (@lem1900434 h1 _27029). Qed.
Lemma lem1900444 (_27029 : real) : (term50 _27029) = (term47 _27029).
Proof. exact (eq_refl (term50 _27029)). Qed.
Lemma lem1900445 (_27029 : real) (h1 : term17) : term47 _27029.
Proof. exact (EQ_MP (@lem1900444 _27029) (@lem1900443 _27029 h1)). Qed.
Lemma lem1900446 (_27029 : real) (_27030 : real) (h1 : term17) : term51 _27029 _27030.
Proof. exact (@lem1900445 _27029 h1 _27030). Qed.
Lemma lem1900447 (_27029 : real) (_27030 : real) : (term51 _27029 _27030) = (term44 _27029 _27030).
Proof. exact (eq_refl (term51 _27029 _27030)). Qed.
Lemma lem1900448 (_27029 : real) (_27030 : real) (h1 : term17) : term44 _27029 _27030.
Proof. exact (EQ_MP (@lem1900447 _27029 _27030) (@lem1900446 _27029 _27030 h1)). Qed.
Lemma lem1900459 (_27029 : real) (_27030 : real) : (term44 _27029 _27030) = (term52 _27029 _27030).
Proof. exact (@lem1900070 (term53 _27030) (term54 _27030 _27029) ((sqrt _27029) = _27030)). Qed.
Lemma lem1900460 (_27029 : real) (_27030 : real) (h1 : term17) : term52 _27029 _27030.
Proof. exact (EQ_MP (@lem1900459 _27029 _27030) (@lem1900448 _27029 _27030 h1)). Qed.
Lemma lem1900464 (x : real) (h1 : term27 x) : term55 x.
Proof. exact (proj2 (@lem1900410 x h1)). Qed.
Lemma lem1900544 (x : real) (h1 : term27 x) : term28 x.
Proof. exact (proj1 (@lem1900410 x h1)). Qed.
Lemma lem1900545 (x : real) (h1 : term27 x) : term56 x.
Proof. exact (fun h0 : term53 x => @lem1900544 x h1). Qed.
Lemma lem1900547 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1900548 (x : real) : (term56 x) = (term28 x).
Proof. exact (@lem1900547 (term28 x)). Qed.
Lemma lem1900549 (x : real) (h1 : term27 x) : term28 x.
Proof. exact (EQ_MP (@lem1900548 x) (@lem1900545 x h1)). Qed.
Lemma lem1900551 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1900552 (x : real) : (term40 x) = (term40 x).
Proof. exact (@lem1900551 (term40 x)). Qed.
Lemma lem1900553 (x : real) : term58 x.
Proof. exact (fun h0 : term59 x => @lem1900552 x). Qed.
Lemma lem1900555 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1900556 (x : real) : (term58 x) = ((term40 x) = (term40 x)).
Proof. exact (@lem1900555 ((term40 x) = (term40 x))). Qed.
Lemma lem1900557 (x : real) : (term40 x) = (term40 x).
Proof. exact (EQ_MP (@lem1900556 x) (@lem1900553 x)). Qed.
Lemma lem1900563 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1900564 (_27029 : real) (_27030 : real) : (term52 _27029 _27030) = (term60 _27029 _27030).
Proof. exact (@lem1900563 (term54 _27030 _27029) (term53 _27030) ((sqrt _27029) = _27030)). Qed.
Lemma lem1900580 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1900581 (_27029 : real) (_27030 : real) : (term61 _27029 _27030) = (term62 _27029 _27030).
Proof. exact (@lem1900580 ((sqrt _27029) = _27030) (term53 _27030)). Qed.
Lemma lem1900589 (_27030 : real) (_27029 : real) : (term63 _27030 _27029) = (term63 _27030 _27029).
Proof. exact (eq_refl (term63 _27030 _27029)). Qed.
Lemma lem1900590 (_27029 : real) (_27030 : real) : (term60 _27029 _27030) = (term64 _27029 _27030).
Proof. exact (MK_COMB (@lem1900589 _27030 _27029) (@lem1900581 _27029 _27030)). Qed.
Lemma lem1900594 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1900595 (_27029 : real) (_27030 : real) : (term64 _27029 _27030) = (term65 _27029 _27030).
Proof. exact (@lem1900594 ((sqrt _27029) = _27030) (term54 _27030 _27029) (term53 _27030)). Qed.
Lemma lem1900615 (_27029 : real) (_27030 : real) : (term60 _27029 _27030) = (term65 _27029 _27030).
Proof. exact (TRANS (@lem1900590 _27029 _27030) (@lem1900595 _27029 _27030)). Qed.
Lemma lem1900616 (_27029 : real) (_27030 : real) : (term52 _27029 _27030) = (term65 _27029 _27030).
Proof. exact (TRANS (@lem1900564 _27029 _27030) (@lem1900615 _27029 _27030)). Qed.
Lemma lem1900617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1900618 (_27029 : real) (_27030 : real) : (term66 _27029 _27030) = (term67 _27029 _27030).
Proof. exact (MK_COMB (@lem1900617) (@lem1900616 _27029 _27030)). Qed.
Lemma lem1900634 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1900635 (_27029 : real) (_27030 : real) : (term39 _27030 _27029) = (term68 _27029 _27030).
Proof. exact (@lem1900634 (term54 _27030 _27029) (term53 _27030)). Qed.
Lemma lem1900643 (_27029 : real) (_27030 : real) : (term69 _27029 _27030) = (term69 _27029 _27030).
Proof. exact (eq_refl (term69 _27029 _27030)). Qed.
Lemma lem1900644 (_27029 : real) (_27030 : real) : (term70 _27030 _27029) = (term65 _27029 _27030).
Proof. exact (MK_COMB (@lem1900643 _27029 _27030) (@lem1900635 _27029 _27030)). Qed.
Lemma lem1900655 (_27029 : real) (_27030 : real) : ((term52 _27029 _27030) = (term70 _27030 _27029)) = ((term65 _27029 _27030) = (term65 _27029 _27030)).
Proof. exact (MK_COMB (@lem1900618 _27029 _27030) (@lem1900644 _27029 _27030)). Qed.
Lemma lem1900657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1900658 (x : Prop) : (x = x) = True.
Proof. exact (@lem1900657 Prop x). Qed.
Lemma lem1900659 (_27029 : real) (_27030 : real) : ((term65 _27029 _27030) = (term65 _27029 _27030)) = True.
Proof. exact (@lem1900658 (term65 _27029 _27030)). Qed.
Lemma lem1900660 (_27030 : real) (_27029 : real) : ((term52 _27029 _27030) = (term70 _27030 _27029)) = True.
Proof. exact (TRANS (@lem1900655 _27029 _27030) (@lem1900659 _27029 _27030)). Qed.
Lemma lem1900661 (_27030 : real) (_27029 : real) : True = ((term52 _27029 _27030) = (term70 _27030 _27029)).
Proof. exact (SYM (@lem1900660 _27030 _27029)). Qed.
Lemma lem1900662 (_27030 : real) (_27029 : real) : (term52 _27029 _27030) = (term70 _27030 _27029).
Proof. exact (EQ_MP (@lem1900661 _27030 _27029) (@lem0)). Qed.
Lemma lem1900663 (_27030 : real) (_27029 : real) (h1 : term17) : term70 _27030 _27029.
Proof. exact (EQ_MP (@lem1900662 _27030 _27029) (@lem1900460 _27029 _27030 h1)). Qed.
Lemma lem1900665 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1900666 (_27029 : real) (_27030 : real) : (term70 _27030 _27029) = (term72 _27029 _27030).
Proof. exact (@lem1900665 (term39 _27030 _27029) ((sqrt _27029) = _27030)). Qed.
Lemma lem1900668 (a : Prop) (b : Prop) : (term73 a b) = (term74 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1900669 (_27030 : real) (_27029 : real) : (term75 _27030 _27029) = (term76 _27030 _27029).
Proof. exact (@lem1900668 (term53 _27030) (term54 _27030 _27029)). Qed.
Lemma lem1900671 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1900672 (_27030 : real) : (term78 _27030) = (term28 _27030).
Proof. exact (@lem1900671 (term28 _27030)). Qed.
Lemma lem1900673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1900674 (_27030 : real) : (term79 _27030) = (term80 _27030).
Proof. exact (MK_COMB (@lem1900673) (@lem1900672 _27030)). Qed.
Lemma lem1900676 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1900677 (_27030 : real) (_27029 : real) : (term81 _27030 _27029) = ((term40 _27030) = _27029).
Proof. exact (@lem1900676 ((term40 _27030) = _27029)). Qed.
Lemma lem1900678 (_27030 : real) (_27029 : real) : (term76 _27030 _27029) = (term45 _27030 _27029).
Proof. exact (MK_COMB (@lem1900674 _27030) (@lem1900677 _27030 _27029)). Qed.
Lemma lem1900679 (_27030 : real) (_27029 : real) : (term75 _27030 _27029) = (term45 _27030 _27029).
Proof. exact (TRANS (@lem1900669 _27030 _27029) (@lem1900678 _27030 _27029)). Qed.
Lemma lem1900680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1900681 (_27030 : real) (_27029 : real) : (term82 _27030 _27029) = (term83 _27030 _27029).
Proof. exact (MK_COMB (@lem1900680) (@lem1900679 _27030 _27029)). Qed.
Lemma lem1900682 (_27029 : real) (_27030 : real) : ((sqrt _27029) = _27030) = ((sqrt _27029) = _27030).
Proof. exact (eq_refl ((sqrt _27029) = _27030)). Qed.
Lemma lem1900683 (_27029 : real) (_27030 : real) : (term72 _27029 _27030) = (term20 _27029 _27030).
Proof. exact (MK_COMB (@lem1900681 _27030 _27029) (@lem1900682 _27029 _27030)). Qed.
Lemma lem1900684 (_27029 : real) (_27030 : real) : (term70 _27030 _27029) = (term20 _27029 _27030).
Proof. exact (TRANS (@lem1900666 _27029 _27030) (@lem1900683 _27029 _27030)). Qed.
Lemma lem1900686 (x : real) (h1 : term27 x) : term84 x.
Proof. exact (conj (@lem1900549 x h1) (@lem1900557 x)). Qed.
Lemma lem1900688 (_27029 : real) (_27030 : real) (h1 : term17) : term20 _27029 _27030.
Proof. exact (EQ_MP (@lem1900684 _27029 _27030) (@lem1900663 _27030 _27029 h1)). Qed.
Lemma lem1900689 (x : real) (h1 : term17) : term85 x.
Proof. exact (@lem1900688 (term40 x) x h1). Qed.
Lemma lem1900692 (x : real) (h1 : term17) (h2 : term27 x) : (term29 x) = x.
Proof. exact (@lem1900689 x h1 (@lem1900686 x h2)). Qed.
Lemma lem1900693 (x : real) (h1 : term17) (h2 : term27 x) : term86 x.
Proof. exact (fun h0 : term55 x => @lem1900692 x h1 h2). Qed.
Lemma lem1900695 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1900696 (x : real) : (term86 x) = ((term29 x) = x).
Proof. exact (@lem1900695 ((term29 x) = x)). Qed.
Lemma lem1900697 (x : real) (h1 : term17) (h2 : term27 x) : (term29 x) = x.
Proof. exact (EQ_MP (@lem1900696 x) (@lem1900693 x h1 h2)). Qed.
Lemma lem1900700 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1900702 (x : real) : (term55 x) = (term87 x).
Proof. exact (@lem1900700 ((term29 x) = x)). Qed.
Lemma lem1900705 (x : real) (h1 : term27 x) : term87 x.
Proof. exact (EQ_MP (@lem1900702 x) (@lem1900464 x h1)). Qed.
Lemma lem1900708 (x : real) (h1 : term17) (h2 : term27 x) : False.
Proof. exact (@lem1900705 x h2 (@lem1900697 x h1 h2)). Qed.
Lemma lem1900709 (x : real) (h1 : term17) (h2 : term27 x) : term88.
Proof. exact (fun h0 : ~ False => @lem1900708 x h1 h2). Qed.
Lemma lem1900711 (p : Prop) : (term57 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1900712 : term88 = False.
Proof. exact (@lem1900711 False). Qed.
Lemma lem1900713 (x : real) (h1 : term17) (h2 : term27 x) : False.
Proof. exact (EQ_MP (@lem1900712) (@lem1900709 x h1 h2)). Qed.
Lemma lem1900714 (x : real) (h1 : term17) (h2 : term27 x) : (term27 x) = False.
Proof. exact (prop_ext (fun h3 : term27 x => @lem1900713 x h1 h2) (fun h3 : False => @lem1900410 x h2)). Qed.
Lemma lem1900715 (x : real) (h1 : term17) (h2 : term27 x) : False.
Proof. exact (EQ_MP (@lem1900714 x h1 h2) (@lem1900410 x h2)). Qed.
Lemma lem1900716 (h1 : term17) (h2 : term10) : False.
Proof. exact (ex_elim (@lem1900253 h2) (fun x : real => fun h0 : term36 x => @lem1900715 x h1 h0)). Qed.
Lemma lem1900717 (h1 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1900716 h0 h1). Qed.
Lemma lem1900718 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1900719 (h1 : term10) : term16.
Proof. exact (EQ_MP (@lem1900718) (@lem1900717 h1)). Qed.
Lemma lem1900720 : term19.
Proof. exact (fun h0 : term10 => @lem1900719 h0). Qed.
Lemma lem1900721 : term11.
Proof. exact (EQ_MP (@lem1900181) (@lem1900720)). Qed.
Lemma lem1900723 : term11.
Proof. exact (@lem1900090 (@lem1900721)). Qed.
Lemma lem1900724 (h1 : term10) : term15.
Proof. exact (@lem1900723 (@lem1900075 h1)). Qed.
Lemma lem1900725 (h1 : term10) : False.
Proof. exact (@lem1900724 h1 (@lem1900060)). Qed.
Lemma lem1900726 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1900725 h1) (fun h2 : False => @lem1900075 h1)). Qed.
Lemma lem1900727 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1900726 h1) (@lem1900075 h1)). Qed.
Lemma lem1900728 : term9.
Proof. exact (fun h0 : term10 => @lem1900727 h0). Qed.
Lemma lem1900729 : term8.
Proof. exact (EQ_MP (@lem1900074) (@lem1900728)). Qed.
