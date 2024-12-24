Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_POW_2_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import SQRT_WORKS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1945304 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1945305 : term1 = term2.
Proof. exact (@lem1945304 term1). Qed.
Lemma lem1945306 : term2 = term1.
Proof. exact (SYM (@lem1945305)). Qed.
Lemma lem1945307 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1945310 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1945311 : term5.
Proof. exact (fun h0 : term4 => @lem1945310 h0). Qed.
Lemma lem1945312 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1945313 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1945314 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1945312 h2 (@lem1945313 h1)). Qed.
Lemma lem1945315 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1945314 h1 h0). Qed.
Lemma lem1945316 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1945317 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1945315 h1 (@lem1945316 h2)). Qed.
Lemma lem1945318 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1945317 h0 h1). Qed.
Lemma lem1945319 : term7.
Proof. exact (fun h0 : term5 => @lem1945318 h0). Qed.
Lemma lem1945322 : term5.
Proof. exact (@lem1945319 (@lem1945311)). Qed.
Lemma lem1945332 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1945333 : term8 = term9.
Proof. exact (@lem1945332 term10). Qed.
Lemma lem1945342 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1945349 : term4 = term12.
Proof. exact (MK_COMB (@lem1945342) (@lem1945333)). Qed.
Lemma lem1945358 (x : real) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1945359 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1945358 x)). Qed.
Lemma lem1945360 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945361 : term10 = term10.
Proof. exact (MK_COMB (@lem1945360) (@lem1945359)). Qed.
Lemma lem1945362 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1945363 : term9 = term9.
Proof. exact (MK_COMB (@lem1945362) (@lem1945361)). Qed.
Lemma lem1945368 (x : real) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1945369 : term16 = term16.
Proof. exact (fun_ext (fun x : real => @lem1945368 x)). Qed.
Lemma lem1945370 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945371 : term1 = term1.
Proof. exact (MK_COMB (@lem1945370) (@lem1945369)). Qed.
Lemma lem1945372 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1945373 : term3 = term3.
Proof. exact (MK_COMB (@lem1945372) (@lem1945371)). Qed.
Lemma lem1945374 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1945375 : term11 = term11.
Proof. exact (MK_COMB (@lem1945374) (@lem1945373)). Qed.
Lemma lem1945376 : term12 = term12.
Proof. exact (MK_COMB (@lem1945375) (@lem1945363)). Qed.
Lemma lem1945399 : term4 = term12.
Proof. exact (TRANS (@lem1945349) (@lem1945376)). Qed.
Lemma lem1945400 : term12 = term4.
Proof. exact (SYM (@lem1945399)). Qed.
Lemma lem1945401 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1945402 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1945409 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem17362 (term19 x) ((term20 x) = x)). Qed.
Lemma lem1945410 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1945411 : term3 = term23.
Proof. exact (@lem1945410 term16). Qed.
Lemma lem1945412 (x : real) : (term24 x) = (term15 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1945413 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1945414 (x : real) : (term25 x) = (term17 x).
Proof. exact (MK_COMB (@lem1945413) (@lem1945412 x)). Qed.
Lemma lem1945415 (x : real) : (term25 x) = (term18 x).
Proof. exact (TRANS (@lem1945414 x) (@lem1945409 x)). Qed.
Lemma lem1945416 : term26 = term27.
Proof. exact (fun_ext (fun x : real => @lem1945415 x)). Qed.
Lemma lem1945417 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1945418 : term23 = term28.
Proof. exact (MK_COMB (@lem1945417) (@lem1945416)). Qed.
Lemma lem1945471 : term3 = term28.
Proof. exact (TRANS (@lem1945411) (@lem1945418)). Qed.
Lemma lem1945472 (h1 : term3) : term28.
Proof. exact (EQ_MP (@lem1945471) (@lem1945401 h1)). Qed.
Lemma lem1945483 (x : real) : (term13 x) = (term29 x).
Proof. exact (@lem17265 (term19 x) (term30 x)). Qed.
Lemma lem1945484 : term14 = term31.
Proof. exact (fun_ext (fun x : real => @lem1945483 x)). Qed.
Lemma lem1945485 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945538 : term10 = term32.
Proof. exact (MK_COMB (@lem1945485) (@lem1945484)). Qed.
Lemma lem1945539 (h1 : term10) : term32.
Proof. exact (EQ_MP (@lem1945538) (@lem1945402 h1)). Qed.
Lemma lem1945585 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1945586 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1945585 x)). Qed.
Lemma lem1945587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945588 : term32 = term32.
Proof. exact (MK_COMB (@lem1945587) (@lem1945586)). Qed.
Lemma lem1945589 (h1 : term10) : term32.
Proof. exact (EQ_MP (@lem1945588) (@lem1945539 h1)). Qed.
Lemma lem1945621 (x : real) (h1 : term18 x) : term18 x.
Proof. exact (h1). Qed.
Lemma lem1945641 (x : real) : (term29 x) = (term33 x).
Proof. exact (@lem19490 (term34 x) (term35 x) ((term20 x) = x)). Qed.
Lemma lem1945642 : term31 = term36.
Proof. exact (fun_ext (fun x : real => @lem1945641 x)). Qed.
Lemma lem1945643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945645 : term32 = term37.
Proof. exact (MK_COMB (@lem1945643) (@lem1945642)). Qed.
Lemma lem1945646 (h1 : term10) : term37.
Proof. exact (EQ_MP (@lem1945645) (@lem1945589 h1)). Qed.
Lemma lem1945655 (_27301 : real) (h1 : term10) : term38 _27301.
Proof. exact (@lem1945646 h1 _27301). Qed.
Lemma lem1945656 (_27301 : real) : (term38 _27301) = (term33 _27301).
Proof. exact (eq_refl (term38 _27301)). Qed.
Lemma lem1945657 (_27301 : real) (h1 : term10) : term33 _27301.
Proof. exact (EQ_MP (@lem1945656 _27301) (@lem1945655 _27301 h1)). Qed.
Lemma lem1945663 (x : real) (h1 : term18 x) : term39 x.
Proof. exact (proj2 (@lem1945621 x h1)). Qed.
Lemma lem1945675 (_27301 : real) (h1 : term10) : term40 _27301.
Proof. exact (proj2 (@lem1945657 _27301 h1)). Qed.
Lemma lem1945755 (x : real) (h1 : term18 x) : term19 x.
Proof. exact (proj1 (@lem1945621 x h1)). Qed.
Lemma lem1945756 (x : real) (h1 : term18 x) : term41 x.
Proof. exact (fun h0 : term35 x => @lem1945755 x h1). Qed.
Lemma lem1945758 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1945759 (x : real) : (term41 x) = (term19 x).
Proof. exact (@lem1945758 (term19 x)). Qed.
Lemma lem1945760 (x : real) (h1 : term18 x) : term19 x.
Proof. exact (EQ_MP (@lem1945759 x) (@lem1945756 x h1)). Qed.
Lemma lem1945766 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1945767 (_27301 : real) : (term40 _27301) = (term43 _27301).
Proof. exact (@lem1945766 ((term20 _27301) = _27301) (term35 _27301)). Qed.
Lemma lem1945775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1945776 (_27301 : real) : (term44 _27301) = (term45 _27301).
Proof. exact (MK_COMB (@lem1945775) (@lem1945767 _27301)). Qed.
Lemma lem1945784 (_27301 : real) : (term43 _27301) = (term43 _27301).
Proof. exact (eq_refl (term43 _27301)). Qed.
Lemma lem1945785 (_27301 : real) : ((term40 _27301) = (term43 _27301)) = ((term43 _27301) = (term43 _27301)).
Proof. exact (MK_COMB (@lem1945776 _27301) (@lem1945784 _27301)). Qed.
Lemma lem1945787 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1945788 (x : Prop) : (x = x) = True.
Proof. exact (@lem1945787 Prop x). Qed.
Lemma lem1945789 (_27301 : real) : ((term43 _27301) = (term43 _27301)) = True.
Proof. exact (@lem1945788 (term43 _27301)). Qed.
Lemma lem1945790 (_27301 : real) : ((term40 _27301) = (term43 _27301)) = True.
Proof. exact (TRANS (@lem1945785 _27301) (@lem1945789 _27301)). Qed.
Lemma lem1945791 (_27301 : real) : True = ((term40 _27301) = (term43 _27301)).
Proof. exact (SYM (@lem1945790 _27301)). Qed.
Lemma lem1945792 (_27301 : real) : (term40 _27301) = (term43 _27301).
Proof. exact (EQ_MP (@lem1945791 _27301) (@lem0)). Qed.
Lemma lem1945793 (_27301 : real) (h1 : term10) : term43 _27301.
Proof. exact (EQ_MP (@lem1945792 _27301) (@lem1945675 _27301 h1)). Qed.
Lemma lem1945795 (b : Prop) (a : Prop) : (a \/ b) = (term46 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1945796 (_27301 : real) : (term43 _27301) = (term47 _27301).
Proof. exact (@lem1945795 (term35 _27301) ((term20 _27301) = _27301)). Qed.
Lemma lem1945798 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1945799 (_27301 : real) : (term49 _27301) = (term19 _27301).
Proof. exact (@lem1945798 (term19 _27301)). Qed.
Lemma lem1945800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1945801 (_27301 : real) : (term50 _27301) = (term51 _27301).
Proof. exact (MK_COMB (@lem1945800) (@lem1945799 _27301)). Qed.
Lemma lem1945802 (_27301 : real) : ((term20 _27301) = _27301) = ((term20 _27301) = _27301).
Proof. exact (eq_refl ((term20 _27301) = _27301)). Qed.
Lemma lem1945803 (_27301 : real) : (term47 _27301) = (term15 _27301).
Proof. exact (MK_COMB (@lem1945801 _27301) (@lem1945802 _27301)). Qed.
Lemma lem1945804 (_27301 : real) : (term43 _27301) = (term15 _27301).
Proof. exact (TRANS (@lem1945796 _27301) (@lem1945803 _27301)). Qed.
Lemma lem1945807 (_27301 : real) (h1 : term10) : term15 _27301.
Proof. exact (EQ_MP (@lem1945804 _27301) (@lem1945793 _27301 h1)). Qed.
Lemma lem1945808 (x : real) (h1 : term10) : term15 x.
Proof. exact (@lem1945807 x h1). Qed.
Lemma lem1945811 (x : real) (h1 : term10) (h2 : term18 x) : (term20 x) = x.
Proof. exact (@lem1945808 x h1 (@lem1945760 x h2)). Qed.
Lemma lem1945812 (x : real) (h1 : term10) (h2 : term18 x) : term52 x.
Proof. exact (fun h0 : term39 x => @lem1945811 x h1 h2). Qed.
Lemma lem1945814 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1945815 (x : real) : (term52 x) = ((term20 x) = x).
Proof. exact (@lem1945814 ((term20 x) = x)). Qed.
Lemma lem1945816 (x : real) (h1 : term10) (h2 : term18 x) : (term20 x) = x.
Proof. exact (EQ_MP (@lem1945815 x) (@lem1945812 x h1 h2)). Qed.
Lemma lem1945819 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1945821 (x : real) : (term39 x) = (term53 x).
Proof. exact (@lem1945819 ((term20 x) = x)). Qed.
Lemma lem1945824 (x : real) (h1 : term18 x) : term53 x.
Proof. exact (EQ_MP (@lem1945821 x) (@lem1945663 x h1)). Qed.
Lemma lem1945827 (x : real) (h1 : term10) (h2 : term18 x) : False.
Proof. exact (@lem1945824 x h2 (@lem1945816 x h1 h2)). Qed.
Lemma lem1945828 (x : real) (h1 : term10) (h2 : term18 x) : term54.
Proof. exact (fun h0 : ~ False => @lem1945827 x h1 h2). Qed.
Lemma lem1945830 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1945831 : term54 = False.
Proof. exact (@lem1945830 False). Qed.
Lemma lem1945832 (x : real) (h1 : term10) (h2 : term18 x) : False.
Proof. exact (EQ_MP (@lem1945831) (@lem1945828 x h1 h2)). Qed.
Lemma lem1945833 (x : real) (h1 : term10) (h2 : term18 x) : (term18 x) = False.
Proof. exact (prop_ext (fun h3 : term18 x => @lem1945832 x h1 h2) (fun h3 : False => @lem1945621 x h2)). Qed.
Lemma lem1945834 (x : real) (h1 : term10) (h2 : term18 x) : False.
Proof. exact (EQ_MP (@lem1945833 x h1 h2) (@lem1945621 x h2)). Qed.
Lemma lem1945835 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem1945472 h2) (fun x : real => fun h0 : term27 x => @lem1945834 x h1 h0)). Qed.
Lemma lem1945836 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1945835 h0 h1). Qed.
Lemma lem1945837 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1945838 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem1945837) (@lem1945836 h1)). Qed.
Lemma lem1945839 : term12.
Proof. exact (fun h0 : term3 => @lem1945838 h0). Qed.
Lemma lem1945840 : term4.
Proof. exact (EQ_MP (@lem1945400) (@lem1945839)). Qed.
Lemma lem1945842 : term4.
Proof. exact (@lem1945322 (@lem1945840)). Qed.
Lemma lem1945843 (h1 : term3) : term8.
Proof. exact (@lem1945842 (@lem1945307 h1)). Qed.
Lemma lem1945844 (h1 : term3) : False.
Proof. exact (@lem1945843 h1 (@lem1943636)). Qed.
Lemma lem1945845 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1945844 h1) (fun h2 : False => @lem1945307 h1)). Qed.
Lemma lem1945846 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1945845 h1) (@lem1945307 h1)). Qed.
Lemma lem1945847 : term2.
Proof. exact (fun h0 : term3 => @lem1945846 h0). Qed.
Lemma lem1945848 : term1.
Proof. exact (EQ_MP (@lem1945306) (@lem1945847)). Qed.
