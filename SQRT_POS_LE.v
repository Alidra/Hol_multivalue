Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_POS_LE_term_abbrevs.
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
Lemma lem1944758 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1944759 : term1 = term2.
Proof. exact (@lem1944758 term1). Qed.
Lemma lem1944760 : term2 = term1.
Proof. exact (SYM (@lem1944759)). Qed.
Lemma lem1944761 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1944764 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1944765 : term5.
Proof. exact (fun h0 : term4 => @lem1944764 h0). Qed.
Lemma lem1944766 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1944767 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1944768 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1944766 h2 (@lem1944767 h1)). Qed.
Lemma lem1944769 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1944768 h1 h0). Qed.
Lemma lem1944770 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1944771 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1944769 h1 (@lem1944770 h2)). Qed.
Lemma lem1944772 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1944771 h0 h1). Qed.
Lemma lem1944773 : term7.
Proof. exact (fun h0 : term5 => @lem1944772 h0). Qed.
Lemma lem1944776 : term5.
Proof. exact (@lem1944773 (@lem1944765)). Qed.
Lemma lem1944786 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1944787 : term8 = term9.
Proof. exact (@lem1944786 term10). Qed.
Lemma lem1944796 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1944803 : term4 = term12.
Proof. exact (MK_COMB (@lem1944796) (@lem1944787)). Qed.
Lemma lem1944812 (x : real) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1944813 : term14 = term14.
Proof. exact (fun_ext (fun x : real => @lem1944812 x)). Qed.
Lemma lem1944814 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944815 : term10 = term10.
Proof. exact (MK_COMB (@lem1944814) (@lem1944813)). Qed.
Lemma lem1944816 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1944817 : term9 = term9.
Proof. exact (MK_COMB (@lem1944816) (@lem1944815)). Qed.
Lemma lem1944822 (x : real) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1944823 : term16 = term16.
Proof. exact (fun_ext (fun x : real => @lem1944822 x)). Qed.
Lemma lem1944824 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944825 : term1 = term1.
Proof. exact (MK_COMB (@lem1944824) (@lem1944823)). Qed.
Lemma lem1944826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1944827 : term3 = term3.
Proof. exact (MK_COMB (@lem1944826) (@lem1944825)). Qed.
Lemma lem1944828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1944829 : term11 = term11.
Proof. exact (MK_COMB (@lem1944828) (@lem1944827)). Qed.
Lemma lem1944830 : term12 = term12.
Proof. exact (MK_COMB (@lem1944829) (@lem1944817)). Qed.
Lemma lem1944853 : term4 = term12.
Proof. exact (TRANS (@lem1944803) (@lem1944830)). Qed.
Lemma lem1944854 : term12 = term4.
Proof. exact (SYM (@lem1944853)). Qed.
Lemma lem1944855 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1944856 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1944863 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem17362 (term19 x) (term20 x)). Qed.
Lemma lem1944864 (P : real -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1944865 : term3 = term23.
Proof. exact (@lem1944864 term16). Qed.
Lemma lem1944866 (x : real) : (term24 x) = (term15 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1944867 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1944868 (x : real) : (term25 x) = (term17 x).
Proof. exact (MK_COMB (@lem1944867) (@lem1944866 x)). Qed.
Lemma lem1944869 (x : real) : (term25 x) = (term18 x).
Proof. exact (TRANS (@lem1944868 x) (@lem1944863 x)). Qed.
Lemma lem1944870 : term26 = term27.
Proof. exact (fun_ext (fun x : real => @lem1944869 x)). Qed.
Lemma lem1944871 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1944872 : term23 = term28.
Proof. exact (MK_COMB (@lem1944871) (@lem1944870)). Qed.
Lemma lem1944925 : term3 = term28.
Proof. exact (TRANS (@lem1944865) (@lem1944872)). Qed.
Lemma lem1944926 (h1 : term3) : term28.
Proof. exact (EQ_MP (@lem1944925) (@lem1944855 h1)). Qed.
Lemma lem1944937 (x : real) : (term13 x) = (term29 x).
Proof. exact (@lem17265 (term19 x) (term30 x)). Qed.
Lemma lem1944938 : term14 = term31.
Proof. exact (fun_ext (fun x : real => @lem1944937 x)). Qed.
Lemma lem1944939 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944992 : term10 = term32.
Proof. exact (MK_COMB (@lem1944939) (@lem1944938)). Qed.
Lemma lem1944993 (h1 : term10) : term32.
Proof. exact (EQ_MP (@lem1944992) (@lem1944856 h1)). Qed.
Lemma lem1945039 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1945040 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1945039 x)). Qed.
Lemma lem1945041 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945042 : term32 = term32.
Proof. exact (MK_COMB (@lem1945041) (@lem1945040)). Qed.
Lemma lem1945043 (h1 : term10) : term32.
Proof. exact (EQ_MP (@lem1945042) (@lem1944993 h1)). Qed.
Lemma lem1945069 (x : real) (h1 : term18 x) : term18 x.
Proof. exact (h1). Qed.
Lemma lem1945089 (x : real) : (term29 x) = (term33 x).
Proof. exact (@lem19490 (term20 x) (term34 x) ((term35 x) = x)). Qed.
Lemma lem1945090 : term31 = term36.
Proof. exact (fun_ext (fun x : real => @lem1945089 x)). Qed.
Lemma lem1945091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1945093 : term32 = term37.
Proof. exact (MK_COMB (@lem1945091) (@lem1945090)). Qed.
Lemma lem1945094 (h1 : term10) : term37.
Proof. exact (EQ_MP (@lem1945093) (@lem1945043 h1)). Qed.
Lemma lem1945103 (_27282 : real) (h1 : term10) : term38 _27282.
Proof. exact (@lem1945094 h1 _27282). Qed.
Lemma lem1945104 (_27282 : real) : (term38 _27282) = (term33 _27282).
Proof. exact (eq_refl (term38 _27282)). Qed.
Lemma lem1945105 (_27282 : real) (h1 : term10) : term33 _27282.
Proof. exact (EQ_MP (@lem1945104 _27282) (@lem1945103 _27282 h1)). Qed.
Lemma lem1945111 (x : real) (h1 : term18 x) : term39 x.
Proof. exact (proj2 (@lem1945069 x h1)). Qed.
Lemma lem1945117 (_27282 : real) (h1 : term10) : term40 _27282.
Proof. exact (proj1 (@lem1945105 _27282 h1)). Qed.
Lemma lem1945203 (x : real) (h1 : term18 x) : term19 x.
Proof. exact (proj1 (@lem1945069 x h1)). Qed.
Lemma lem1945204 (x : real) (h1 : term18 x) : term41 x.
Proof. exact (fun h0 : term34 x => @lem1945203 x h1). Qed.
Lemma lem1945206 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1945207 (x : real) : (term41 x) = (term19 x).
Proof. exact (@lem1945206 (term19 x)). Qed.
Lemma lem1945208 (x : real) (h1 : term18 x) : term19 x.
Proof. exact (EQ_MP (@lem1945207 x) (@lem1945204 x h1)). Qed.
Lemma lem1945214 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1945215 (_27282 : real) : (term40 _27282) = (term43 _27282).
Proof. exact (@lem1945214 (term20 _27282) (term34 _27282)). Qed.
Lemma lem1945221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1945222 (_27282 : real) : (term44 _27282) = (term45 _27282).
Proof. exact (MK_COMB (@lem1945221) (@lem1945215 _27282)). Qed.
Lemma lem1945228 (_27282 : real) : (term43 _27282) = (term43 _27282).
Proof. exact (eq_refl (term43 _27282)). Qed.
Lemma lem1945229 (_27282 : real) : ((term40 _27282) = (term43 _27282)) = ((term43 _27282) = (term43 _27282)).
Proof. exact (MK_COMB (@lem1945222 _27282) (@lem1945228 _27282)). Qed.
Lemma lem1945231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1945232 (x : Prop) : (x = x) = True.
Proof. exact (@lem1945231 Prop x). Qed.
Lemma lem1945233 (_27282 : real) : ((term43 _27282) = (term43 _27282)) = True.
Proof. exact (@lem1945232 (term43 _27282)). Qed.
Lemma lem1945234 (_27282 : real) : ((term40 _27282) = (term43 _27282)) = True.
Proof. exact (TRANS (@lem1945229 _27282) (@lem1945233 _27282)). Qed.
Lemma lem1945235 (_27282 : real) : True = ((term40 _27282) = (term43 _27282)).
Proof. exact (SYM (@lem1945234 _27282)). Qed.
Lemma lem1945236 (_27282 : real) : (term40 _27282) = (term43 _27282).
Proof. exact (EQ_MP (@lem1945235 _27282) (@lem0)). Qed.
Lemma lem1945237 (_27282 : real) (h1 : term10) : term43 _27282.
Proof. exact (EQ_MP (@lem1945236 _27282) (@lem1945117 _27282 h1)). Qed.
Lemma lem1945239 (b : Prop) (a : Prop) : (a \/ b) = (term46 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1945240 (_27282 : real) : (term43 _27282) = (term47 _27282).
Proof. exact (@lem1945239 (term34 _27282) (term20 _27282)). Qed.
Lemma lem1945242 (a : Prop) : (term48 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1945243 (_27282 : real) : (term49 _27282) = (term19 _27282).
Proof. exact (@lem1945242 (term19 _27282)). Qed.
Lemma lem1945244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1945245 (_27282 : real) : (term50 _27282) = (term51 _27282).
Proof. exact (MK_COMB (@lem1945244) (@lem1945243 _27282)). Qed.
Lemma lem1945246 (_27282 : real) : (term20 _27282) = (term20 _27282).
Proof. exact (eq_refl (term20 _27282)). Qed.
Lemma lem1945247 (_27282 : real) : (term47 _27282) = (term15 _27282).
Proof. exact (MK_COMB (@lem1945245 _27282) (@lem1945246 _27282)). Qed.
Lemma lem1945248 (_27282 : real) : (term43 _27282) = (term15 _27282).
Proof. exact (TRANS (@lem1945240 _27282) (@lem1945247 _27282)). Qed.
Lemma lem1945251 (_27282 : real) (h1 : term10) : term15 _27282.
Proof. exact (EQ_MP (@lem1945248 _27282) (@lem1945237 _27282 h1)). Qed.
Lemma lem1945252 (x : real) (h1 : term10) : term15 x.
Proof. exact (@lem1945251 x h1). Qed.
Lemma lem1945255 (x : real) (h1 : term10) (h2 : term18 x) : term20 x.
Proof. exact (@lem1945252 x h1 (@lem1945208 x h2)). Qed.
Lemma lem1945256 (x : real) (h1 : term10) (h2 : term18 x) : term52 x.
Proof. exact (fun h0 : term39 x => @lem1945255 x h1 h2). Qed.
Lemma lem1945258 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1945259 (x : real) : (term52 x) = (term20 x).
Proof. exact (@lem1945258 (term20 x)). Qed.
Lemma lem1945260 (x : real) (h1 : term10) (h2 : term18 x) : term20 x.
Proof. exact (EQ_MP (@lem1945259 x) (@lem1945256 x h1 h2)). Qed.
Lemma lem1945263 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1945265 (x : real) : (term39 x) = (term53 x).
Proof. exact (@lem1945263 (term20 x)). Qed.
Lemma lem1945268 (x : real) (h1 : term18 x) : term53 x.
Proof. exact (EQ_MP (@lem1945265 x) (@lem1945111 x h1)). Qed.
Lemma lem1945271 (x : real) (h1 : term10) (h2 : term18 x) : False.
Proof. exact (@lem1945268 x h2 (@lem1945260 x h1 h2)). Qed.
Lemma lem1945272 (x : real) (h1 : term10) (h2 : term18 x) : term54.
Proof. exact (fun h0 : ~ False => @lem1945271 x h1 h2). Qed.
Lemma lem1945274 (p : Prop) : (term42 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1945275 : term54 = False.
Proof. exact (@lem1945274 False). Qed.
Lemma lem1945276 (x : real) (h1 : term10) (h2 : term18 x) : False.
Proof. exact (EQ_MP (@lem1945275) (@lem1945272 x h1 h2)). Qed.
Lemma lem1945277 (x : real) (h1 : term10) (h2 : term18 x) : (term18 x) = False.
Proof. exact (prop_ext (fun h3 : term18 x => @lem1945276 x h1 h2) (fun h3 : False => @lem1945069 x h2)). Qed.
Lemma lem1945278 (x : real) (h1 : term10) (h2 : term18 x) : False.
Proof. exact (EQ_MP (@lem1945277 x h1 h2) (@lem1945069 x h2)). Qed.
Lemma lem1945279 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem1944926 h2) (fun x : real => fun h0 : term27 x => @lem1945278 x h1 h0)). Qed.
Lemma lem1945280 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1945279 h0 h1). Qed.
Lemma lem1945281 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1945282 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem1945281) (@lem1945280 h1)). Qed.
Lemma lem1945283 : term12.
Proof. exact (fun h0 : term3 => @lem1945282 h0). Qed.
Lemma lem1945284 : term4.
Proof. exact (EQ_MP (@lem1944854) (@lem1945283)). Qed.
Lemma lem1945286 : term4.
Proof. exact (@lem1944776 (@lem1945284)). Qed.
Lemma lem1945287 (h1 : term3) : term8.
Proof. exact (@lem1945286 (@lem1944761 h1)). Qed.
Lemma lem1945288 (h1 : term3) : False.
Proof. exact (@lem1945287 h1 (@lem1943636)). Qed.
Lemma lem1945289 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1945288 h1) (fun h2 : False => @lem1944761 h1)). Qed.
Lemma lem1945290 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1945289 h1) (@lem1944761 h1)). Qed.
Lemma lem1945291 : term2.
Proof. exact (fun h0 : term3 => @lem1945290 h0). Qed.
Lemma lem1945292 : term1.
Proof. exact (EQ_MP (@lem1944760) (@lem1945291)). Qed.
