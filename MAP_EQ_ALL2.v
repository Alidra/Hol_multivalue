Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_EQ_ALL2_term_abbrevs.
Require Import ALL2_spec.
Require Import CONS_11_spec.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem1124172 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1124173 {_26486 : Type'} (P : type1143 _26486) : term0 _26486 P.
Proof. exact (@lem1124172 _26486 P). Qed.
Lemma lem1124174 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term1 _26486 _26497 f.
Proof. exact (@lem1124173 _26486 (term2 _26486 _26497 f)). Qed.
Lemma lem1124175 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term3 _26486 _26497 f) = (term4 _26486 _26497 f).
Proof. exact (eq_refl (term3 _26486 _26497 f)). Qed.
Lemma lem1124176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1124177 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term5 _26486 _26497 f) = (term6 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124176) (@lem1124175 _26486 _26497 f)). Qed.
Lemma lem1124178 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) : (term7 _26486 _26497 f t) = (term8 _26486 _26497 t f).
Proof. exact (eq_refl (term7 _26486 _26497 f t)). Qed.
Lemma lem1124179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124180 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) : (term9 _26486 _26497 f t) = (term10 _26486 _26497 t f).
Proof. exact (MK_COMB (@lem1124179) (@lem1124178 _26486 _26497 t f)). Qed.
Lemma lem1124181 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term11 _26486 _26497 f h t) = (term12 _26486 _26497 h t f).
Proof. exact (eq_refl (term11 _26486 _26497 f h t)). Qed.
Lemma lem1124182 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term13 _26486 _26497 f h t) = (term14 _26486 _26497 h t f).
Proof. exact (MK_COMB (@lem1124180 _26486 _26497 t f) (@lem1124181 _26486 _26497 h t f)). Qed.
Lemma lem1124183 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) : (term15 _26486 _26497 f h) = (term16 _26486 _26497 h f).
Proof. exact (fun_ext (fun t : list _26486 => @lem1124182 _26486 _26497 h t f)). Qed.
Lemma lem1124184 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124185 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) : (term17 _26486 _26497 f h) = (term18 _26486 _26497 h f).
Proof. exact (MK_COMB (@lem1124184 _26486) (@lem1124183 _26486 _26497 h f)). Qed.
Lemma lem1124186 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term19 _26486 _26497 f) = (term20 _26486 _26497 f).
Proof. exact (fun_ext (fun h : _26486 => @lem1124185 _26486 _26497 h f)). Qed.
Lemma lem1124187 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124188 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term21 _26486 _26497 f) = (term22 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124187 _26486) (@lem1124186 _26486 _26497 f)). Qed.
Lemma lem1124189 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term23 _26486 _26497 f) = (term24 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124177 _26486 _26497 f) (@lem1124188 _26486 _26497 f)). Qed.
Lemma lem1124190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124191 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term25 _26486 _26497 f) = (term26 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124190) (@lem1124189 _26486 _26497 f)). Qed.
Lemma lem1124192 {_26486 _26497 : Type'} (l : list _26486) (f : _26486 -> _26497) : (term7 _26486 _26497 f l) = (term8 _26486 _26497 l f).
Proof. exact (eq_refl (term7 _26486 _26497 f l)). Qed.
Lemma lem1124193 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term27 _26486 _26497 f) = (term2 _26486 _26497 f).
Proof. exact (fun_ext (fun l : list _26486 => @lem1124192 _26486 _26497 l f)). Qed.
Lemma lem1124194 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124195 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term28 _26486 _26497 f) = (term29 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124194 _26486) (@lem1124193 _26486 _26497 f)). Qed.
Lemma lem1124196 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term1 _26486 _26497 f) = (term30 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124191 _26486 _26497 f) (@lem1124195 _26486 _26497 f)). Qed.
Lemma lem1124197 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term30 _26486 _26497 f.
Proof. exact (EQ_MP (@lem1124196 _26486 _26497 f) (@lem1124174 _26486 _26497 f)). Qed.
Lemma lem1124198 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (h1 : term8 _26486 _26497 t f) : term8 _26486 _26497 t f.
Proof. exact (h1). Qed.
Lemma lem1124200 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1124201 {_26486 : Type'} (P : type1143 _26486) : term0 _26486 P.
Proof. exact (@lem1124200 _26486 P). Qed.
Lemma lem1124202 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term31 _26486 _26497 f.
Proof. exact (@lem1124201 _26486 (term32 _26486 _26497 f)). Qed.
Lemma lem1124203 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term33 _26486 _26497 f) = (term34 _26486 _26497 f).
Proof. exact (eq_refl (term33 _26486 _26497 f)). Qed.
Lemma lem1124204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1124205 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term35 _26486 _26497 f) = (term36 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124204) (@lem1124203 _26486 _26497 f)). Qed.
Lemma lem1124206 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (term37 _26486 _26497 f t) = (term38 _26486 _26497 f t).
Proof. exact (eq_refl (term37 _26486 _26497 f t)). Qed.
Lemma lem1124207 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124208 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (term39 _26486 _26497 f t) = (term40 _26486 _26497 f t).
Proof. exact (MK_COMB (@lem1124207) (@lem1124206 _26486 _26497 f t)). Qed.
Lemma lem1124209 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term41 _26486 _26497 f h t) = (term42 _26486 _26497 f h t).
Proof. exact (eq_refl (term41 _26486 _26497 f h t)). Qed.
Lemma lem1124210 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term43 _26486 _26497 f h t) = (term44 _26486 _26497 f h t).
Proof. exact (MK_COMB (@lem1124208 _26486 _26497 f t) (@lem1124209 _26486 _26497 f h t)). Qed.
Lemma lem1124211 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (term45 _26486 _26497 f h) = (term46 _26486 _26497 f h).
Proof. exact (fun_ext (fun t : list _26486 => @lem1124210 _26486 _26497 f h t)). Qed.
Lemma lem1124212 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124213 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (term47 _26486 _26497 f h) = (term48 _26486 _26497 f h).
Proof. exact (MK_COMB (@lem1124212 _26486) (@lem1124211 _26486 _26497 f h)). Qed.
Lemma lem1124214 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term49 _26486 _26497 f) = (term50 _26486 _26497 f).
Proof. exact (fun_ext (fun h : _26486 => @lem1124213 _26486 _26497 f h)). Qed.
Lemma lem1124215 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124216 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term51 _26486 _26497 f) = (term52 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124215 _26486) (@lem1124214 _26486 _26497 f)). Qed.
Lemma lem1124217 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term53 _26486 _26497 f) = (term54 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124205 _26486 _26497 f) (@lem1124216 _26486 _26497 f)). Qed.
Lemma lem1124218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124219 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term55 _26486 _26497 f) = (term56 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124218) (@lem1124217 _26486 _26497 f)). Qed.
Lemma lem1124220 {_26486 _26497 : Type'} (f : _26486 -> _26497) (m : list _26486) : (term37 _26486 _26497 f m) = (term38 _26486 _26497 f m).
Proof. exact (eq_refl (term37 _26486 _26497 f m)). Qed.
Lemma lem1124221 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term57 _26486 _26497 f) = (term32 _26486 _26497 f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1124220 _26486 _26497 f m)). Qed.
Lemma lem1124222 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124223 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term58 _26486 _26497 f) = (term4 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124222 _26486) (@lem1124221 _26486 _26497 f)). Qed.
Lemma lem1124224 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term31 _26486 _26497 f) = (term59 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124219 _26486 _26497 f) (@lem1124223 _26486 _26497 f)). Qed.
Lemma lem1124225 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term59 _26486 _26497 f.
Proof. exact (EQ_MP (@lem1124224 _26486 _26497 f) (@lem1124202 _26486 _26497 f)). Qed.
Lemma lem1124232 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1124233 {_26486 : Type'} (P : type1143 _26486) : term0 _26486 P.
Proof. exact (@lem1124232 _26486 P). Qed.
Lemma lem1124234 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : term60 _26486 _26497 h t f.
Proof. exact (@lem1124233 _26486 (term61 _26486 _26497 h t f)). Qed.
Lemma lem1124235 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term62 _26486 _26497 h t f) = (term63 _26486 _26497 h t f).
Proof. exact (eq_refl (term62 _26486 _26497 h t f)). Qed.
Lemma lem1124236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1124237 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term64 _26486 _26497 h t f) = (term65 _26486 _26497 h t f).
Proof. exact (MK_COMB (@lem1124236) (@lem1124235 _26486 _26497 h t f)). Qed.
Lemma lem1124238 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term66 _26486 _26497 h t f t') = (term67 _26486 _26497 h t f t').
Proof. exact (eq_refl (term66 _26486 _26497 h t f t')). Qed.
Lemma lem1124239 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124240 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term68 _26486 _26497 h t f t') = (term69 _26486 _26497 h t f t').
Proof. exact (MK_COMB (@lem1124239) (@lem1124238 _26486 _26497 h t f t')). Qed.
Lemma lem1124241 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h' : _26486) (t' : list _26486) : (term70 _26486 _26497 h t f h' t') = (term71 _26486 _26497 h t f h' t').
Proof. exact (eq_refl (term70 _26486 _26497 h t f h' t')). Qed.
Lemma lem1124242 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h' : _26486) (t' : list _26486) : (term72 _26486 _26497 h t f h' t') = (term73 _26486 _26497 h t f h' t').
Proof. exact (MK_COMB (@lem1124240 _26486 _26497 h t f t') (@lem1124241 _26486 _26497 h t f h' t')). Qed.
Lemma lem1124243 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h' : _26486) : (term74 _26486 _26497 h t f h') = (term75 _26486 _26497 h t f h').
Proof. exact (fun_ext (fun t' : list _26486 => @lem1124242 _26486 _26497 h t f h' t')). Qed.
Lemma lem1124244 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124245 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h' : _26486) : (term76 _26486 _26497 h t f h') = (term77 _26486 _26497 h t f h').
Proof. exact (MK_COMB (@lem1124244 _26486) (@lem1124243 _26486 _26497 h t f h')). Qed.
Lemma lem1124246 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term78 _26486 _26497 h t f) = (term79 _26486 _26497 h t f).
Proof. exact (fun_ext (fun h' : _26486 => @lem1124245 _26486 _26497 h t f h')). Qed.
Lemma lem1124247 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124248 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term80 _26486 _26497 h t f) = (term81 _26486 _26497 h t f).
Proof. exact (MK_COMB (@lem1124247 _26486) (@lem1124246 _26486 _26497 h t f)). Qed.
Lemma lem1124249 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term82 _26486 _26497 h t f) = (term83 _26486 _26497 h t f).
Proof. exact (MK_COMB (@lem1124237 _26486 _26497 h t f) (@lem1124248 _26486 _26497 h t f)). Qed.
Lemma lem1124250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124251 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term84 _26486 _26497 h t f) = (term85 _26486 _26497 h t f).
Proof. exact (MK_COMB (@lem1124250) (@lem1124249 _26486 _26497 h t f)). Qed.
Lemma lem1124252 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : (term66 _26486 _26497 h t f m) = (term67 _26486 _26497 h t f m).
Proof. exact (eq_refl (term66 _26486 _26497 h t f m)). Qed.
Lemma lem1124253 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term86 _26486 _26497 h t f) = (term61 _26486 _26497 h t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1124252 _26486 _26497 h t f m)). Qed.
Lemma lem1124254 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124255 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term87 _26486 _26497 h t f) = (term12 _26486 _26497 h t f).
Proof. exact (MK_COMB (@lem1124254 _26486) (@lem1124253 _26486 _26497 h t f)). Qed.
Lemma lem1124256 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term60 _26486 _26497 h t f) = (term88 _26486 _26497 h t f).
Proof. exact (MK_COMB (@lem1124251 _26486 _26497 h t f) (@lem1124255 _26486 _26497 h t f)). Qed.
Lemma lem1124257 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : term88 _26486 _26497 h t f.
Proof. exact (EQ_MP (@lem1124256 _26486 _26497 h t f) (@lem1124234 _26486 _26497 h t f)). Qed.
Lemma lem1124258 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term67 _26486 _26497 h t f t') : term67 _26486 _26497 h t f t'.
Proof. exact (h1). Qed.
Lemma lem1124298 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1124299 {_26486 : Type'} (P : type1402 _26486) : (@ALL2 _26486 _26486 P (@nil _26486) (@nil _26486)) = True.
Proof. exact (@lem1124298 _26486 _26486 P). Qed.
Lemma lem1124300 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term89 _26486 _26497 f) = True.
Proof. exact (@lem1124299 _26486 (term90 _26486 _26497 f)). Qed.
Lemma lem1124301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124302 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term91 _26486 _26497 f) = (imp True).
Proof. exact (MK_COMB (@lem1124301) (@lem1124300 _26486 _26497 f)). Qed.
Lemma lem1124304 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1124305 {_26497 : Type'} (x : list _26497) : (x = x) = True.
Proof. exact (@lem1124304 (list _26497) x). Qed.
Lemma lem1124306 {_26486 _26497 : Type'} (f : _26486 -> _26497) : ((@List.map _26486 _26497 f (@nil _26486)) = (@List.map _26486 _26497 f (@nil _26486))) = True.
Proof. exact (@lem1124305 _26497 (@List.map _26486 _26497 f (@nil _26486))). Qed.
Lemma lem1124307 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term34 _26486 _26497 f) = (True -> True).
Proof. exact (MK_COMB (@lem1124302 _26486 _26497 f) (@lem1124306 _26486 _26497 f)). Qed.
Lemma lem1124309 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1124310 : (True -> True) = True.
Proof. exact (@lem1124309 True). Qed.
Lemma lem1124311 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term34 _26486 _26497 f) = True.
Proof. exact (TRANS (@lem1124307 _26486 _26497 f) (@lem1124310)). Qed.
Lemma lem1124312 {_26486 _26497 : Type'} (f : _26486 -> _26497) : True = (term34 _26486 _26497 f).
Proof. exact (SYM (@lem1124311 _26486 _26497 f)). Qed.
Lemma lem1124313 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term34 _26486 _26497 f.
Proof. exact (EQ_MP (@lem1124312 _26486 _26497 f) (@lem0)). Qed.
Lemma lem1124326 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term92 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1124327 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term93 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1124326 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1124332 {A B : Type'} : term94 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1124333 {A B : Type'} (f : A -> B) : term95 A B f.
Proof. exact (@lem1124332 A B f). Qed.
Lemma lem1124334 {A B : Type'} (f : A -> B) : (term95 A B f) = (term96 A B f).
Proof. exact (eq_refl (term95 A B f)). Qed.
Lemma lem1124335 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (EQ_MP (@lem1124334 A B f) (@lem1124333 A B f)). Qed.
Lemma lem1124336 {A B : Type'} (f : A -> B) (h : A) : term97 A B f h.
Proof. exact (@lem1124335 A B f h). Qed.
Lemma lem1124337 {A B : Type'} (h : A) (f : A -> B) : (term97 A B f h) = (term98 A B h f).
Proof. exact (eq_refl (term97 A B f h)). Qed.
Lemma lem1124338 {A B : Type'} (h : A) (f : A -> B) : term98 A B h f.
Proof. exact (EQ_MP (@lem1124337 A B h f) (@lem1124336 A B f h)). Qed.
Lemma lem1124339 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term99 A B h f t.
Proof. exact (@lem1124338 A B h f t). Qed.
Lemma lem1124340 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term99 A B h f t) = ((term100 A B f h t) = (term101 A B h f t)).
Proof. exact (eq_refl (term99 A B h f t)). Qed.
Lemma lem1124342 {A B : Type'} : term102 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1124343 {A B : Type'} (f : A -> B) : term103 A B f.
Proof. exact (@lem1124342 A B f). Qed.
Lemma lem1124344 {A B : Type'} (f : A -> B) : (term103 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term103 A B f)). Qed.
Lemma lem1124351 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term104 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1124327 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1124352 {_26486 : Type'} (P : type1402 _26486) (h2' : _26486) (t2 : list _26486) : (term105 _26486 P h2' t2) = False.
Proof. exact (@lem1124351 _26486 _26486 P h2' t2). Qed.
Lemma lem1124353 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term106 _26486 _26497 f h t) = False.
Proof. exact (@lem1124352 _26486 (term90 _26486 _26497 f) h t). Qed.
Lemma lem1124354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124355 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term107 _26486 _26497 f h t) = (imp False).
Proof. exact (MK_COMB (@lem1124354) (@lem1124353 _26486 _26497 f h t)). Qed.
Lemma lem1124359 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1124344 A B f) (@lem1124343 A B f)). Qed.
Lemma lem1124360 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f (@nil _26486)) = (@nil _26497).
Proof. exact (@lem1124359 _26486 _26497 f). Qed.
Lemma lem1124361 {_26497 : Type'} : (@eq (list _26497)) = (@eq (list _26497)).
Proof. exact (eq_refl (@eq (list _26497))). Qed.
Lemma lem1124362 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term108 _26486 _26497 f) = (@eq (list _26497) (@nil _26497)).
Proof. exact (MK_COMB (@lem1124361 _26497) (@lem1124360 _26486 _26497 f)). Qed.
Lemma lem1124364 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term100 A B f h t) = (term101 A B h f t).
Proof. exact (EQ_MP (@lem1124340 A B h f t) (@lem1124339 A B h f t)). Qed.
Lemma lem1124365 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term100 _26486 _26497 f h t) = (term101 _26486 _26497 h f t).
Proof. exact (@lem1124364 _26486 _26497 h f t). Qed.
Lemma lem1124366 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : ((@List.map _26486 _26497 f (@nil _26486)) = (term100 _26486 _26497 f h t)) = ((@nil _26497) = (term101 _26486 _26497 h f t)).
Proof. exact (MK_COMB (@lem1124362 _26486 _26497 f) (@lem1124365 _26486 _26497 h f t)). Qed.
Lemma lem1124369 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term42 _26486 _26497 f h t) = (term109 _26486 _26497 h f t).
Proof. exact (MK_COMB (@lem1124355 _26486 _26497 f h t) (@lem1124366 _26486 _26497 h f t)). Qed.
Lemma lem1124371 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1124372 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term109 _26486 _26497 h f t) = True.
Proof. exact (@lem1124371 ((@nil _26497) = (term101 _26486 _26497 h f t))). Qed.
Lemma lem1124373 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term42 _26486 _26497 f h t) = True.
Proof. exact (TRANS (@lem1124369 _26486 _26497 h f t) (@lem1124372 _26486 _26497 h f t)). Qed.
Lemma lem1124374 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : True = (term42 _26486 _26497 f h t).
Proof. exact (SYM (@lem1124373 _26486 _26497 f h t)). Qed.
Lemma lem1124375 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : term42 _26486 _26497 f h t.
Proof. exact (EQ_MP (@lem1124374 _26486 _26497 f h t) (@lem0)). Qed.
Lemma lem1124388 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term92 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1124394 {A B : Type'} : term94 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1124395 {A B : Type'} (f : A -> B) : term95 A B f.
Proof. exact (@lem1124394 A B f). Qed.
Lemma lem1124396 {A B : Type'} (f : A -> B) : (term95 A B f) = (term96 A B f).
Proof. exact (eq_refl (term95 A B f)). Qed.
Lemma lem1124397 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (EQ_MP (@lem1124396 A B f) (@lem1124395 A B f)). Qed.
Lemma lem1124398 {A B : Type'} (f : A -> B) (h : A) : term97 A B f h.
Proof. exact (@lem1124397 A B f h). Qed.
Lemma lem1124399 {A B : Type'} (h : A) (f : A -> B) : (term97 A B f h) = (term98 A B h f).
Proof. exact (eq_refl (term97 A B f h)). Qed.
Lemma lem1124400 {A B : Type'} (h : A) (f : A -> B) : term98 A B h f.
Proof. exact (EQ_MP (@lem1124399 A B h f) (@lem1124398 A B f h)). Qed.
Lemma lem1124401 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term99 A B h f t.
Proof. exact (@lem1124400 A B h f t). Qed.
Lemma lem1124402 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term99 A B h f t) = ((term100 A B f h t) = (term101 A B h f t)).
Proof. exact (eq_refl (term99 A B h f t)). Qed.
Lemma lem1124404 {A B : Type'} : term102 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1124405 {A B : Type'} (f : A -> B) : term103 A B f.
Proof. exact (@lem1124404 A B f). Qed.
Lemma lem1124406 {A B : Type'} (f : A -> B) : (term103 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term103 A B f)). Qed.
Lemma lem1124416 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term110 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1124388 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1124417 {_26486 : Type'} (P : type1402 _26486) (h1' : _26486) (t1 : list _26486) : (term111 _26486 P h1' t1) = False.
Proof. exact (@lem1124416 _26486 _26486 P h1' t1). Qed.
Lemma lem1124418 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term112 _26486 _26497 f h t) = False.
Proof. exact (@lem1124417 _26486 (term90 _26486 _26497 f) h t). Qed.
Lemma lem1124419 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124420 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term113 _26486 _26497 f h t) = (imp False).
Proof. exact (MK_COMB (@lem1124419) (@lem1124418 _26486 _26497 f h t)). Qed.
Lemma lem1124424 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term100 A B f h t) = (term101 A B h f t).
Proof. exact (EQ_MP (@lem1124402 A B h f t) (@lem1124401 A B h f t)). Qed.
Lemma lem1124425 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term100 _26486 _26497 f h t) = (term101 _26486 _26497 h f t).
Proof. exact (@lem1124424 _26486 _26497 h f t). Qed.
Lemma lem1124426 {_26497 : Type'} : (@eq (list _26497)) = (@eq (list _26497)).
Proof. exact (eq_refl (@eq (list _26497))). Qed.
Lemma lem1124427 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term114 _26486 _26497 f h t) = (term115 _26486 _26497 h f t).
Proof. exact (MK_COMB (@lem1124426 _26497) (@lem1124425 _26486 _26497 h f t)). Qed.
Lemma lem1124429 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1124406 A B f) (@lem1124405 A B f)). Qed.
Lemma lem1124430 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f (@nil _26486)) = (@nil _26497).
Proof. exact (@lem1124429 _26486 _26497 f). Qed.
Lemma lem1124431 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : ((term100 _26486 _26497 f h t) = (@List.map _26486 _26497 f (@nil _26486))) = ((term101 _26486 _26497 h f t) = (@nil _26497)).
Proof. exact (MK_COMB (@lem1124427 _26486 _26497 h f t) (@lem1124430 _26486 _26497 f)). Qed.
Lemma lem1124434 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term63 _26486 _26497 h t f) = (term116 _26486 _26497 h f t).
Proof. exact (MK_COMB (@lem1124420 _26486 _26497 f h t) (@lem1124431 _26486 _26497 h f t)). Qed.
Lemma lem1124436 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1124437 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term116 _26486 _26497 h f t) = True.
Proof. exact (@lem1124436 ((term101 _26486 _26497 h f t) = (@nil _26497))). Qed.
Lemma lem1124438 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : (term63 _26486 _26497 h t f) = True.
Proof. exact (TRANS (@lem1124434 _26486 _26497 h f t) (@lem1124437 _26486 _26497 h f t)). Qed.
Lemma lem1124439 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : True = (term63 _26486 _26497 h t f).
Proof. exact (SYM (@lem1124438 _26486 _26497 h t f)). Qed.
Lemma lem1124440 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : term63 _26486 _26497 h t f.
Proof. exact (EQ_MP (@lem1124439 _26486 _26497 h t f) (@lem0)). Qed.
Lemma lem1124441 {A : Type'} (h1' : A) : term117 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1124442 {A : Type'} (h1' : A) : (term117 A h1') = (term118 A h1').
Proof. exact (eq_refl (term117 A h1')). Qed.
Lemma lem1124443 {A : Type'} (h1' : A) : term118 A h1'.
Proof. exact (EQ_MP (@lem1124442 A h1') (@lem1124441 A h1')). Qed.
Lemma lem1124444 {A : Type'} (h1' : A) (h2' : A) : term119 A h1' h2'.
Proof. exact (@lem1124443 A h1' h2'). Qed.
Lemma lem1124445 {A : Type'} (h1' : A) (h2' : A) : (term119 A h1' h2') = (term120 A h1' h2').
Proof. exact (eq_refl (term119 A h1' h2')). Qed.
Lemma lem1124446 {A : Type'} (h1' : A) (h2' : A) : term120 A h1' h2'.
Proof. exact (EQ_MP (@lem1124445 A h1' h2') (@lem1124444 A h1' h2')). Qed.
Lemma lem1124447 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term121 A h1' h2' t1.
Proof. exact (@lem1124446 A h1' h2' t1). Qed.
Lemma lem1124448 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term121 A h1' h2' t1) = (term122 A h1' h2' t1).
Proof. exact (eq_refl (term121 A h1' h2' t1)). Qed.
Lemma lem1124449 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term122 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1124448 A h1' h2' t1) (@lem1124447 A h1' h2' t1)). Qed.
Lemma lem1124450 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term123 A h1' h2' t1 t2.
Proof. exact (@lem1124449 A h1' h2' t1 t2). Qed.
Lemma lem1124451 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term123 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term124 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term123 A h1' h2' t1 t2)). Qed.
Lemma lem1124453 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term92 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1124454 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term93 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1124453 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1124459 {A B : Type'} : term94 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1124460 {A B : Type'} (f : A -> B) : term95 A B f.
Proof. exact (@lem1124459 A B f). Qed.
Lemma lem1124461 {A B : Type'} (f : A -> B) : (term95 A B f) = (term96 A B f).
Proof. exact (eq_refl (term95 A B f)). Qed.
Lemma lem1124462 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (EQ_MP (@lem1124461 A B f) (@lem1124460 A B f)). Qed.
Lemma lem1124463 {A B : Type'} (f : A -> B) (h : A) : term97 A B f h.
Proof. exact (@lem1124462 A B f h). Qed.
Lemma lem1124464 {A B : Type'} (h : A) (f : A -> B) : (term97 A B f h) = (term98 A B h f).
Proof. exact (eq_refl (term97 A B f h)). Qed.
Lemma lem1124465 {A B : Type'} (h : A) (f : A -> B) : term98 A B h f.
Proof. exact (EQ_MP (@lem1124464 A B h f) (@lem1124463 A B f h)). Qed.
Lemma lem1124466 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term99 A B h f t.
Proof. exact (@lem1124465 A B h f t). Qed.
Lemma lem1124467 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term99 A B h f t) = ((term100 A B f h t) = (term101 A B h f t)).
Proof. exact (eq_refl (term99 A B h f t)). Qed.
Lemma lem1124483 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term125 _25470 _25471 P h1' t1 h2' t2) = (term126 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1124454 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1124484 {_26486 : Type'} (h1' : _26486) (h2' : _26486) (P : type1402 _26486) (t1 : list _26486) (t2 : list _26486) : (term127 _26486 P h1' t1 h2' t2) = (term128 _26486 h1' h2' P t1 t2).
Proof. exact (@lem1124483 _26486 _26486 h1' h2' P t1 t2). Qed.
Lemma lem1124485 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term129 _26486 _26497 f h t h' t') = (term130 _26486 _26497 h h' f t t').
Proof. exact (@lem1124484 _26486 h h' (term90 _26486 _26497 f) t t'). Qed.
Lemma lem1124489 {A B : Type'} (f : A -> B) (y : A) : (term131 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1124490 {_26486 : Type'} (f : type1402 _26486) (y : _26486) : (term132 _26486 f y) = (f y).
Proof. exact (@lem1124489 _26486 (_26486 -> Prop) f y). Qed.
Lemma lem1124491 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (term133 _26486 _26497 f h) = (term134 _26486 _26497 f h).
Proof. exact (@lem1124490 _26486 (term90 _26486 _26497 f) h). Qed.
Lemma lem1124492 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) : (term134 _26486 _26497 f x) = (term135 _26486 _26497 x f).
Proof. exact (eq_refl (term134 _26486 _26497 f x)). Qed.
Lemma lem1124493 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term136 _26486 _26497 f) = (term90 _26486 _26497 f).
Proof. exact (fun_ext (fun x : _26486 => @lem1124492 _26486 _26497 x f)). Qed.
Lemma lem1124494 {_26486 : Type'} (h : _26486) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1124495 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (term133 _26486 _26497 f h) = (term134 _26486 _26497 f h).
Proof. exact (MK_COMB (@lem1124493 _26486 _26497 f) (@lem1124494 _26486 h)). Qed.
Lemma lem1124496 {_26486 : Type'} : (@eq (_26486 -> Prop)) = (@eq (_26486 -> Prop)).
Proof. exact (eq_refl (@eq (_26486 -> Prop))). Qed.
Lemma lem1124497 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (term137 _26486 _26497 f h) = (term138 _26486 _26497 f h).
Proof. exact (MK_COMB (@lem1124496 _26486) (@lem1124495 _26486 _26497 f h)). Qed.
Lemma lem1124498 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) : (term134 _26486 _26497 f h) = (term135 _26486 _26497 h f).
Proof. exact (eq_refl (term134 _26486 _26497 f h)). Qed.
Lemma lem1124499 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) : ((term133 _26486 _26497 f h) = (term134 _26486 _26497 f h)) = ((term134 _26486 _26497 f h) = (term135 _26486 _26497 h f)).
Proof. exact (MK_COMB (@lem1124497 _26486 _26497 f h) (@lem1124498 _26486 _26497 h f)). Qed.
Lemma lem1124500 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) : (term134 _26486 _26497 f h) = (term135 _26486 _26497 h f).
Proof. exact (EQ_MP (@lem1124499 _26486 _26497 h f) (@lem1124491 _26486 _26497 f h)). Qed.
Lemma lem1124503 {_26486 : Type'} (h' : _26486) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1124504 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term139 _26486 _26497 f h h') = (term140 _26486 _26497 h f h').
Proof. exact (MK_COMB (@lem1124500 _26486 _26497 h f) (@lem1124503 _26486 h')). Qed.
Lemma lem1124506 {A B : Type'} (f : A -> B) (y : A) : (term131 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1124507 {_26486 : Type'} (f : _26486 -> Prop) (y : _26486) : (term141 _26486 f y) = (f y).
Proof. exact (@lem1124506 _26486 Prop f y). Qed.
Lemma lem1124508 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term142 _26486 _26497 h f h') = (term140 _26486 _26497 h f h').
Proof. exact (@lem1124507 _26486 (term135 _26486 _26497 h f) h'). Qed.
Lemma lem1124509 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (y : _26486) : (term140 _26486 _26497 h f y) = ((f h) = (f y)).
Proof. exact (eq_refl (term140 _26486 _26497 h f y)). Qed.
Lemma lem1124510 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) : (term143 _26486 _26497 h f) = (term135 _26486 _26497 h f).
Proof. exact (fun_ext (fun y : _26486 => @lem1124509 _26486 _26497 h f y)). Qed.
Lemma lem1124511 {_26486 : Type'} (h' : _26486) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1124512 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term142 _26486 _26497 h f h') = (term140 _26486 _26497 h f h').
Proof. exact (MK_COMB (@lem1124510 _26486 _26497 h f) (@lem1124511 _26486 h')). Qed.
Lemma lem1124513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1124514 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term144 _26486 _26497 h f h') = (term145 _26486 _26497 h f h').
Proof. exact (MK_COMB (@lem1124513) (@lem1124512 _26486 _26497 h f h')). Qed.
Lemma lem1124515 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term140 _26486 _26497 h f h') = ((f h) = (f h')).
Proof. exact (eq_refl (term140 _26486 _26497 h f h')). Qed.
Lemma lem1124516 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : ((term142 _26486 _26497 h f h') = (term140 _26486 _26497 h f h')) = ((term140 _26486 _26497 h f h') = ((f h) = (f h'))).
Proof. exact (MK_COMB (@lem1124514 _26486 _26497 h f h') (@lem1124515 _26486 _26497 h f h')). Qed.
Lemma lem1124517 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term140 _26486 _26497 h f h') = ((f h) = (f h')).
Proof. exact (EQ_MP (@lem1124516 _26486 _26497 h f h') (@lem1124508 _26486 _26497 h f h')). Qed.
Lemma lem1124520 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term139 _26486 _26497 f h h') = ((f h) = (f h')).
Proof. exact (TRANS (@lem1124504 _26486 _26497 h f h') (@lem1124517 _26486 _26497 h f h')). Qed.
Lemma lem1124521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1124522 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term146 _26486 _26497 f h h') = (term147 _26486 _26497 h f h').
Proof. exact (MK_COMB (@lem1124521) (@lem1124520 _26486 _26497 h f h')). Qed.
Lemma lem1124525 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term148 _26486 _26497 f t t') = (term148 _26486 _26497 f t t').
Proof. exact (eq_refl (term148 _26486 _26497 f t t')). Qed.
Lemma lem1124526 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term130 _26486 _26497 h h' f t t') = (term149 _26486 _26497 h h' f t t').
Proof. exact (MK_COMB (@lem1124522 _26486 _26497 h f h') (@lem1124525 _26486 _26497 f t t')). Qed.
Lemma lem1124529 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term129 _26486 _26497 f h t h' t') = (term149 _26486 _26497 h h' f t t').
Proof. exact (TRANS (@lem1124485 _26486 _26497 h h' f t t') (@lem1124526 _26486 _26497 h h' f t t')). Qed.
Lemma lem1124530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124531 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term150 _26486 _26497 f h t h' t') = (term151 _26486 _26497 h h' f t t').
Proof. exact (MK_COMB (@lem1124530) (@lem1124529 _26486 _26497 h h' f t t')). Qed.
Lemma lem1124535 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term100 A B f h t) = (term101 A B h f t).
Proof. exact (EQ_MP (@lem1124467 A B h f t) (@lem1124466 A B h f t)). Qed.
Lemma lem1124536 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term100 _26486 _26497 f h t) = (term101 _26486 _26497 h f t).
Proof. exact (@lem1124535 _26486 _26497 h f t). Qed.
Lemma lem1124537 {_26497 : Type'} : (@eq (list _26497)) = (@eq (list _26497)).
Proof. exact (eq_refl (@eq (list _26497))). Qed.
Lemma lem1124538 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term114 _26486 _26497 f h t) = (term115 _26486 _26497 h f t).
Proof. exact (MK_COMB (@lem1124537 _26497) (@lem1124536 _26486 _26497 h f t)). Qed.
Lemma lem1124540 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term100 A B f h t) = (term101 A B h f t).
Proof. exact (EQ_MP (@lem1124467 A B h f t) (@lem1124466 A B h f t)). Qed.
Lemma lem1124541 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (t : list _26486) : (term100 _26486 _26497 f h t) = (term101 _26486 _26497 h f t).
Proof. exact (@lem1124540 _26486 _26497 h f t). Qed.
Lemma lem1124542 {_26486 _26497 : Type'} (h' : _26486) (f : _26486 -> _26497) (t' : list _26486) : (term100 _26486 _26497 f h' t') = (term101 _26486 _26497 h' f t').
Proof. exact (@lem1124541 _26486 _26497 h' f t'). Qed.
Lemma lem1124543 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (h' : _26486) (f : _26486 -> _26497) (t' : list _26486) : ((term100 _26486 _26497 f h t) = (term100 _26486 _26497 f h' t')) = ((term101 _26486 _26497 h f t) = (term101 _26486 _26497 h' f t')).
Proof. exact (MK_COMB (@lem1124538 _26486 _26497 h f t) (@lem1124542 _26486 _26497 h' f t')). Qed.
Lemma lem1124545 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term124 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1124451 A h1' h2' t1 t2) (@lem1124450 A h1' h2' t1 t2)). Qed.
Lemma lem1124546 {_26497 : Type'} (h1' : _26497) (h2' : _26497) (t1 : list _26497) (t2 : list _26497) : ((@cons _26497 h1' t1) = (@cons _26497 h2' t2)) = (term124 _26497 h1' h2' t1 t2).
Proof. exact (@lem1124545 _26497 h1' h2' t1 t2). Qed.
Lemma lem1124547 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : ((term101 _26486 _26497 h f t) = (term101 _26486 _26497 h' f t')) = (term152 _26486 _26497 h h' t f t').
Proof. exact (@lem1124546 _26497 (f h) (f h') (@List.map _26486 _26497 f t) (@List.map _26486 _26497 f t')). Qed.
Lemma lem1124554 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : ((term100 _26486 _26497 f h t) = (term100 _26486 _26497 f h' t')) = (term152 _26486 _26497 h h' t f t').
Proof. exact (TRANS (@lem1124543 _26486 _26497 h t h' f t') (@lem1124547 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124555 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term71 _26486 _26497 h t f h' t') = (term153 _26486 _26497 h h' t f t').
Proof. exact (MK_COMB (@lem1124531 _26486 _26497 h h' f t t') (@lem1124554 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124558 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h' : _26486) (t' : list _26486) : (term153 _26486 _26497 h h' t f t') = (term71 _26486 _26497 h t f h' t').
Proof. exact (SYM (@lem1124555 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124560 (p : Prop) : p = (term154 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1124561 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term153 _26486 _26497 h h' t f t') = (term155 _26486 _26497 h h' t f t').
Proof. exact (@lem1124560 (term153 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124562 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term155 _26486 _26497 h h' t f t') = (term153 _26486 _26497 h h' t f t').
Proof. exact (SYM (@lem1124561 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124563 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term156 _26486 _26497 h h' t f t') : term156 _26486 _26497 h h' t f t'.
Proof. exact (h1). Qed.
Lemma lem1124566 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term157 _26486 _26497 h h' t f t') : term157 _26486 _26497 h h' t f t'.
Proof. exact (h1). Qed.
Lemma lem1124567 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term158 _26486 _26497 h h' t f t'.
Proof. exact (fun h0 : term157 _26486 _26497 h h' t f t' => @lem1124566 _26486 _26497 h h' t f t' h0). Qed.
Lemma lem1124568 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term158 _26486 _26497 h h' t f t') : term158 _26486 _26497 h h' t f t'.
Proof. exact (h1). Qed.
Lemma lem1124569 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term157 _26486 _26497 h h' t f t') : term157 _26486 _26497 h h' t f t'.
Proof. exact (h1). Qed.
Lemma lem1124570 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term157 _26486 _26497 h h' t f t') (h2 : term158 _26486 _26497 h h' t f t') : term157 _26486 _26497 h h' t f t'.
Proof. exact (@lem1124568 _26486 _26497 h h' t f t' h2 (@lem1124569 _26486 _26497 h h' t f t' h1)). Qed.
Lemma lem1124571 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term157 _26486 _26497 h h' t f t') : term159 _26486 _26497 h h' t f t'.
Proof. exact (fun h0 : term158 _26486 _26497 h h' t f t' => @lem1124570 _26486 _26497 h h' t f t' h1 h0). Qed.
Lemma lem1124572 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term158 _26486 _26497 h h' t f t') : term158 _26486 _26497 h h' t f t'.
Proof. exact (h1). Qed.
Lemma lem1124573 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term157 _26486 _26497 h h' t f t') (h2 : term158 _26486 _26497 h h' t f t') : term157 _26486 _26497 h h' t f t'.
Proof. exact (@lem1124571 _26486 _26497 h h' t f t' h1 (@lem1124572 _26486 _26497 h h' t f t' h2)). Qed.
Lemma lem1124574 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term158 _26486 _26497 h h' t f t') : term158 _26486 _26497 h h' t f t'.
Proof. exact (fun h0 : term157 _26486 _26497 h h' t f t' => @lem1124573 _26486 _26497 h h' t f t' h0 h1). Qed.
Lemma lem1124575 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term160 _26486 _26497 h h' t f t'.
Proof. exact (fun h0 : term158 _26486 _26497 h h' t f t' => @lem1124574 _26486 _26497 h h' t f t' h0). Qed.
Lemma lem1124578 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term158 _26486 _26497 h h' t f t'.
Proof. exact (@lem1124575 _26486 _26497 h h' t f t' (@lem1124567 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124579 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term158 _26486 _26497 h h' t f t'.
Proof. exact (@lem1124578 _26486 _26497 h h' t f t'). Qed.
Lemma lem1124613 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1124614 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term155 _26486 _26497 h h' t f t') = (term161 _26486 _26497 h h' t f t').
Proof. exact (@lem1124613 (term156 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124616 (t : Prop) : (term162 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1124617 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term161 _26486 _26497 h h' t f t') = (term153 _26486 _26497 h h' t f t').
Proof. exact (@lem1124616 (term153 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124620 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term155 _26486 _26497 h h' t f t') = (term153 _26486 _26497 h h' t f t').
Proof. exact (TRANS (@lem1124614 _26486 _26497 h h' t f t') (@lem1124617 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124625 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term69 _26486 _26497 h t f t') = (term69 _26486 _26497 h t f t').
Proof. exact (eq_refl (term69 _26486 _26497 h t f t')). Qed.
Lemma lem1124626 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term163 _26486 _26497 h h' t f t') = (term164 _26486 _26497 h h' t f t').
Proof. exact (MK_COMB (@lem1124625 _26486 _26497 h t f t') (@lem1124620 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124629 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) : (term10 _26486 _26497 t f) = (term10 _26486 _26497 t f).
Proof. exact (eq_refl (term10 _26486 _26497 t f)). Qed.
Lemma lem1124630 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term157 _26486 _26497 h h' t f t') = (term165 _26486 _26497 h h' t f t').
Proof. exact (MK_COMB (@lem1124629 _26486 _26497 t f) (@lem1124626 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124633 {_26486 _26497 : Type'} (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term166 _26486 _26497 h' t f t') = (term167 _26486 _26497 h' t f t').
Proof. exact (fun_ext (fun h : _26486 => @lem1124630 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124634 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124635 {_26486 _26497 : Type'} (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term168 _26486 _26497 h' t f t') = (term169 _26486 _26497 h' t f t').
Proof. exact (MK_COMB (@lem1124634 _26486) (@lem1124633 _26486 _26497 h' t f t')). Qed.
Lemma lem1124640 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term170 _26486 _26497 t f t') = (term171 _26486 _26497 t f t').
Proof. exact (fun_ext (fun h' : _26486 => @lem1124635 _26486 _26497 h' t f t')). Qed.
Lemma lem1124641 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124642 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term172 _26486 _26497 t f t') = (term173 _26486 _26497 t f t').
Proof. exact (MK_COMB (@lem1124641 _26486) (@lem1124640 _26486 _26497 t f t')). Qed.
Lemma lem1124647 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (term174 _26486 _26497 f t') = (term175 _26486 _26497 f t').
Proof. exact (fun_ext (fun t : list _26486 => @lem1124642 _26486 _26497 t f t')). Qed.
Lemma lem1124648 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124649 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (term176 _26486 _26497 f t') = (term177 _26486 _26497 f t').
Proof. exact (MK_COMB (@lem1124648 _26486) (@lem1124647 _26486 _26497 f t')). Qed.
Lemma lem1124654 {_26486 _26497 : Type'} (t' : list _26486) : (term178 _26486 _26497 t') = (term179 _26486 _26497 t').
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1124649 _26486 _26497 f t')). Qed.
Lemma lem1124655 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1124656 {_26486 _26497 : Type'} (t' : list _26486) : (term180 _26486 _26497 t') = (term181 _26486 _26497 t').
Proof. exact (MK_COMB (@lem1124655 _26486 _26497) (@lem1124654 _26486 _26497 t')). Qed.
Lemma lem1124661 {_26486 _26497 : Type'} : (term182 _26486 _26497) = (term183 _26486 _26497).
Proof. exact (fun_ext (fun t' : list _26486 => @lem1124656 _26486 _26497 t')). Qed.
Lemma lem1124662 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124669 {_26486 _26497 : Type'} : (term184 _26486 _26497) = (term185 _26486 _26497).
Proof. exact (MK_COMB (@lem1124662 _26486) (@lem1124661 _26486 _26497)). Qed.
Lemma lem1124670 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : _18342 = (term186 _26486 _26497).
Proof. exact (h1). Qed.
Lemma lem1124671 {_26486 _26497 : Type'} (f : _26486 -> _26497) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1124672 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (_18342 f) = (term187 _26486 _26497 f).
Proof. exact (MK_COMB (@lem1124670 _26486 _26497 _18342 h1) (@lem1124671 _26486 _26497 f)). Qed.
Lemma lem1124673 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term187 _26486 _26497 f) = (term90 _26486 _26497 f).
Proof. exact (eq_refl (term187 _26486 _26497 f)). Qed.
Lemma lem1124674 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term188 _26486 _26497 _18342 f) = (term188 _26486 _26497 _18342 f).
Proof. exact (eq_refl (term188 _26486 _26497 _18342 f)). Qed.
Lemma lem1124675 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : ((_18342 f) = (term187 _26486 _26497 f)) = ((_18342 f) = (term90 _26486 _26497 f)).
Proof. exact (MK_COMB (@lem1124674 _26486 _26497 _18342 f) (@lem1124673 _26486 _26497 f)). Qed.
Lemma lem1124676 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (_18342 f) = (term90 _26486 _26497 f).
Proof. exact (EQ_MP (@lem1124675 _26486 _26497 _18342 f) (@lem1124672 _26486 _26497 f _18342 h1)). Qed.
Lemma lem1124702 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term152 _26486 _26497 h h' t f t') = (term152 _26486 _26497 h h' t f t').
Proof. exact (eq_refl (term152 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124703 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1124704 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1124706 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term90 _26486 _26497 f) = (_18342 f).
Proof. exact (SYM (@lem1124676 _26486 _26497 f _18342 h1)). Qed.
Lemma lem1124707 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term90 _26486 _26497 f) = (_18342 f).
Proof. exact (@lem1124706 _26486 _26497 f _18342 h1). Qed.
Lemma lem1124708 {_26486 : Type'} : (@ALL2 _26486 _26486) = (@ALL2 _26486 _26486).
Proof. exact (eq_refl (@ALL2 _26486 _26486)). Qed.
Lemma lem1124709 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term189 _26486 _26497 f) = (term190 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1124708 _26486) (@lem1124707 _26486 _26497 f _18342 h1)). Qed.
Lemma lem1124710 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term191 _26486 _26497 f t) = (term192 _26486 _26497 _18342 f t).
Proof. exact (MK_COMB (@lem1124709 _26486 _26497 f _18342 h1) (@lem1124704 _26486 t)). Qed.
Lemma lem1124711 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term148 _26486 _26497 f t t') = (term193 _26486 _26497 _18342 f t t').
Proof. exact (MK_COMB (@lem1124710 _26486 _26497 f t _18342 h1) (@lem1124703 _26486 t')). Qed.
Lemma lem1124722 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term147 _26486 _26497 h f h') = (term147 _26486 _26497 h f h').
Proof. exact (eq_refl (term147 _26486 _26497 h f h')). Qed.
Lemma lem1124723 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term149 _26486 _26497 h h' f t t') = (term194 _26486 _26497 h h' _18342 f t t').
Proof. exact (MK_COMB (@lem1124722 _26486 _26497 h f h') (@lem1124711 _26486 _26497 f t t' _18342 h1)). Qed.
Lemma lem1124724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124725 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term151 _26486 _26497 h h' f t t') = (term195 _26486 _26497 h h' _18342 f t t').
Proof. exact (MK_COMB (@lem1124724) (@lem1124723 _26486 _26497 h h' f t t' _18342 h1)). Qed.
Lemma lem1124726 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term153 _26486 _26497 h h' t f t') = (term196 _26486 _26497 _18342 h h' t f t').
Proof. exact (MK_COMB (@lem1124725 _26486 _26497 h h' f t t' _18342 h1) (@lem1124702 _26486 _26497 h h' t f t')). Qed.
Lemma lem1124743 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : ((term100 _26486 _26497 f h t) = (@List.map _26486 _26497 f t')) = ((term100 _26486 _26497 f h t) = (@List.map _26486 _26497 f t')).
Proof. exact (eq_refl ((term100 _26486 _26497 f h t) = (@List.map _26486 _26497 f t'))). Qed.
Lemma lem1124744 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1124749 {_26486 : Type'} (h : _26486) (t : list _26486) : (@cons _26486 h t) = (@cons _26486 h t).
Proof. exact (eq_refl (@cons _26486 h t)). Qed.
Lemma lem1124751 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term90 _26486 _26497 f) = (_18342 f).
Proof. exact (SYM (@lem1124676 _26486 _26497 f _18342 h1)). Qed.
Lemma lem1124752 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term90 _26486 _26497 f) = (_18342 f).
Proof. exact (@lem1124751 _26486 _26497 f _18342 h1). Qed.
Lemma lem1124753 {_26486 : Type'} : (@ALL2 _26486 _26486) = (@ALL2 _26486 _26486).
Proof. exact (eq_refl (@ALL2 _26486 _26486)). Qed.
Lemma lem1124754 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term189 _26486 _26497 f) = (term190 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1124753 _26486) (@lem1124752 _26486 _26497 f _18342 h1)). Qed.
Lemma lem1124755 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term197 _26486 _26497 f h t) = (term198 _26486 _26497 _18342 f h t).
Proof. exact (MK_COMB (@lem1124754 _26486 _26497 f _18342 h1) (@lem1124749 _26486 h t)). Qed.
Lemma lem1124756 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term199 _26486 _26497 f h t t') = (term200 _26486 _26497 _18342 f h t t').
Proof. exact (MK_COMB (@lem1124755 _26486 _26497 f h t _18342 h1) (@lem1124744 _26486 t')). Qed.
Lemma lem1124757 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124758 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term201 _26486 _26497 f h t t') = (term202 _26486 _26497 _18342 f h t t').
Proof. exact (MK_COMB (@lem1124757) (@lem1124756 _26486 _26497 f h t t' _18342 h1)). Qed.
Lemma lem1124759 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term67 _26486 _26497 h t f t') = (term203 _26486 _26497 _18342 h t f t').
Proof. exact (MK_COMB (@lem1124758 _26486 _26497 f h t t' _18342 h1) (@lem1124743 _26486 _26497 h t f t')). Qed.
Lemma lem1124760 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124761 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term69 _26486 _26497 h t f t') = (term204 _26486 _26497 _18342 h t f t').
Proof. exact (MK_COMB (@lem1124760) (@lem1124759 _26486 _26497 h t f t' _18342 h1)). Qed.
Lemma lem1124762 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term164 _26486 _26497 h h' t f t') = (term205 _26486 _26497 _18342 h h' t f t').
Proof. exact (MK_COMB (@lem1124761 _26486 _26497 h t f t' _18342 h1) (@lem1124726 _26486 _26497 h h' t f t' _18342 h1)). Qed.
Lemma lem1124775 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : ((@List.map _26486 _26497 f t) = (@List.map _26486 _26497 f m)) = ((@List.map _26486 _26497 f t) = (@List.map _26486 _26497 f m)).
Proof. exact (eq_refl ((@List.map _26486 _26497 f t) = (@List.map _26486 _26497 f m))). Qed.
Lemma lem1124776 {_26486 : Type'} (m : list _26486) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1124777 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1124779 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term90 _26486 _26497 f) = (_18342 f).
Proof. exact (SYM (@lem1124676 _26486 _26497 f _18342 h1)). Qed.
Lemma lem1124780 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term90 _26486 _26497 f) = (_18342 f).
Proof. exact (@lem1124779 _26486 _26497 f _18342 h1). Qed.
Lemma lem1124781 {_26486 : Type'} : (@ALL2 _26486 _26486) = (@ALL2 _26486 _26486).
Proof. exact (eq_refl (@ALL2 _26486 _26486)). Qed.
Lemma lem1124782 {_26486 _26497 : Type'} (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term189 _26486 _26497 f) = (term190 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1124781 _26486) (@lem1124780 _26486 _26497 f _18342 h1)). Qed.
Lemma lem1124783 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term191 _26486 _26497 f t) = (term192 _26486 _26497 _18342 f t).
Proof. exact (MK_COMB (@lem1124782 _26486 _26497 f _18342 h1) (@lem1124777 _26486 t)). Qed.
Lemma lem1124784 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) (m : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term148 _26486 _26497 f t m) = (term193 _26486 _26497 _18342 f t m).
Proof. exact (MK_COMB (@lem1124783 _26486 _26497 f t _18342 h1) (@lem1124776 _26486 m)). Qed.
Lemma lem1124785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124786 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) (m : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term206 _26486 _26497 f t m) = (term207 _26486 _26497 _18342 f t m).
Proof. exact (MK_COMB (@lem1124785) (@lem1124784 _26486 _26497 f t m _18342 h1)). Qed.
Lemma lem1124787 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (m : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term208 _26486 _26497 t f m) = (term209 _26486 _26497 _18342 t f m).
Proof. exact (MK_COMB (@lem1124786 _26486 _26497 f t m _18342 h1) (@lem1124775 _26486 _26497 t f m)). Qed.
Lemma lem1124788 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term210 _26486 _26497 t f) = (term211 _26486 _26497 _18342 t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1124787 _26486 _26497 t f m _18342 h1)). Qed.
Lemma lem1124789 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124790 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term8 _26486 _26497 t f) = (term212 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1124789 _26486) (@lem1124788 _26486 _26497 t f _18342 h1)). Qed.
Lemma lem1124791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124792 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term10 _26486 _26497 t f) = (term213 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1124791) (@lem1124790 _26486 _26497 t f _18342 h1)). Qed.
Lemma lem1124793 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term165 _26486 _26497 h h' t f t') = (term214 _26486 _26497 _18342 h h' t f t').
Proof. exact (MK_COMB (@lem1124792 _26486 _26497 t f _18342 h1) (@lem1124762 _26486 _26497 h h' t f t' _18342 h1)). Qed.
Lemma lem1124794 {_26486 _26497 : Type'} (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term167 _26486 _26497 h' t f t') = (term215 _26486 _26497 _18342 h' t f t').
Proof. exact (fun_ext (fun h : _26486 => @lem1124793 _26486 _26497 h h' t f t' _18342 h1)). Qed.
Lemma lem1124795 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124796 {_26486 _26497 : Type'} (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term169 _26486 _26497 h' t f t') = (term216 _26486 _26497 _18342 h' t f t').
Proof. exact (MK_COMB (@lem1124795 _26486) (@lem1124794 _26486 _26497 h' t f t' _18342 h1)). Qed.
Lemma lem1124797 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term171 _26486 _26497 t f t') = (term217 _26486 _26497 _18342 t f t').
Proof. exact (fun_ext (fun h' : _26486 => @lem1124796 _26486 _26497 h' t f t' _18342 h1)). Qed.
Lemma lem1124798 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124799 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term173 _26486 _26497 t f t') = (term218 _26486 _26497 _18342 t f t').
Proof. exact (MK_COMB (@lem1124798 _26486) (@lem1124797 _26486 _26497 t f t' _18342 h1)). Qed.
Lemma lem1124800 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term175 _26486 _26497 f t') = (term219 _26486 _26497 _18342 f t').
Proof. exact (fun_ext (fun t : list _26486 => @lem1124799 _26486 _26497 t f t' _18342 h1)). Qed.
Lemma lem1124801 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124802 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term177 _26486 _26497 f t') = (term220 _26486 _26497 _18342 f t').
Proof. exact (MK_COMB (@lem1124801 _26486) (@lem1124800 _26486 _26497 f t' _18342 h1)). Qed.
Lemma lem1124803 {_26486 _26497 : Type'} (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term179 _26486 _26497 t') = (term221 _26486 _26497 _18342 t').
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1124802 _26486 _26497 f t' _18342 h1)). Qed.
Lemma lem1124804 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1124805 {_26486 _26497 : Type'} (t' : list _26486) (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term181 _26486 _26497 t') = (term222 _26486 _26497 _18342 t').
Proof. exact (MK_COMB (@lem1124804 _26486 _26497) (@lem1124803 _26486 _26497 t' _18342 h1)). Qed.
Lemma lem1124806 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term183 _26486 _26497) = (term223 _26486 _26497 _18342).
Proof. exact (fun_ext (fun t' : list _26486 => @lem1124805 _26486 _26497 t' _18342 h1)). Qed.
Lemma lem1124807 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1124808 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h1 : _18342 = (term186 _26486 _26497)) : (term185 _26486 _26497) = (term224 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124807 _26486) (@lem1124806 _26486 _26497 _18342 h1)). Qed.
Lemma lem1124809 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : term225 _26486 _26497 _18342.
Proof. exact (fun h0 : _18342 = (term186 _26486 _26497) => @lem1124808 _26486 _26497 _18342 h0). Qed.
Lemma lem1124810 {_26486 _26497 : Type'} : term226 _26486 _26497.
Proof. exact (fun _18342 : type545 _26486 _26497 => @lem1124809 _26486 _26497 _18342). Qed.
Lemma lem1124812 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term227 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1124813 {_26486 _26497 : Type'} (P : Prop) (c : type545 _26486 _26497) (Q : type102 _26486 _26497) : term228 _26486 _26497 P c Q.
Proof. exact (@lem1124812 (type545 _26486 _26497) P c Q). Qed.
Lemma lem1124814 {_26486 _26497 : Type'} : term229 _26486 _26497.
Proof. exact (@lem1124813 _26486 _26497 (term185 _26486 _26497) (term186 _26486 _26497) (term230 _26486 _26497)). Qed.
Lemma lem1124815 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term231 _26486 _26497 _18342) = (term224 _26486 _26497 _18342).
Proof. exact (eq_refl (term231 _26486 _26497 _18342)). Qed.
Lemma lem1124816 {_26486 _26497 : Type'} : (term232 _26486 _26497) = (term232 _26486 _26497).
Proof. exact (eq_refl (term232 _26486 _26497)). Qed.
Lemma lem1124817 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : ((term185 _26486 _26497) = (term231 _26486 _26497 _18342)) = ((term185 _26486 _26497) = (term224 _26486 _26497 _18342)).
Proof. exact (MK_COMB (@lem1124816 _26486 _26497) (@lem1124815 _26486 _26497 _18342)). Qed.
Lemma lem1124818 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term233 _26486 _26497 _18342) = (term233 _26486 _26497 _18342).
Proof. exact (eq_refl (term233 _26486 _26497 _18342)). Qed.
Lemma lem1124819 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term234 _26486 _26497 _18342) = (term225 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124818 _26486 _26497 _18342) (@lem1124817 _26486 _26497 _18342)). Qed.
Lemma lem1124820 {_26486 _26497 : Type'} : (term235 _26486 _26497) = (term236 _26486 _26497).
Proof. exact (fun_ext (fun _18342 : type545 _26486 _26497 => @lem1124819 _26486 _26497 _18342)). Qed.
Lemma lem1124821 {_26486 _26497 : Type'} : (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)) = (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)).
Proof. exact (eq_refl (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop))). Qed.
Lemma lem1124822 {_26486 _26497 : Type'} : (term237 _26486 _26497) = (term226 _26486 _26497).
Proof. exact (MK_COMB (@lem1124821 _26486 _26497) (@lem1124820 _26486 _26497)). Qed.
Lemma lem1124823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124824 {_26486 _26497 : Type'} : (term238 _26486 _26497) = (term239 _26486 _26497).
Proof. exact (MK_COMB (@lem1124823) (@lem1124822 _26486 _26497)). Qed.
Lemma lem1124825 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term231 _26486 _26497 _18342) = (term224 _26486 _26497 _18342).
Proof. exact (eq_refl (term231 _26486 _26497 _18342)). Qed.
Lemma lem1124826 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term233 _26486 _26497 _18342) = (term233 _26486 _26497 _18342).
Proof. exact (eq_refl (term233 _26486 _26497 _18342)). Qed.
Lemma lem1124827 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term240 _26486 _26497 _18342) = (term241 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124826 _26486 _26497 _18342) (@lem1124825 _26486 _26497 _18342)). Qed.
Lemma lem1124828 {_26486 _26497 : Type'} : (term242 _26486 _26497) = (term243 _26486 _26497).
Proof. exact (fun_ext (fun _18342 : type545 _26486 _26497 => @lem1124827 _26486 _26497 _18342)). Qed.
Lemma lem1124829 {_26486 _26497 : Type'} : (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)) = (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)).
Proof. exact (eq_refl (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop))). Qed.
Lemma lem1124830 {_26486 _26497 : Type'} : (term244 _26486 _26497) = (term245 _26486 _26497).
Proof. exact (MK_COMB (@lem1124829 _26486 _26497) (@lem1124828 _26486 _26497)). Qed.
Lemma lem1124831 {_26486 _26497 : Type'} : (term232 _26486 _26497) = (term232 _26486 _26497).
Proof. exact (eq_refl (term232 _26486 _26497)). Qed.
Lemma lem1124832 {_26486 _26497 : Type'} : ((term185 _26486 _26497) = (term244 _26486 _26497)) = ((term185 _26486 _26497) = (term245 _26486 _26497)).
Proof. exact (MK_COMB (@lem1124831 _26486 _26497) (@lem1124830 _26486 _26497)). Qed.
Lemma lem1124833 {_26486 _26497 : Type'} : (term229 _26486 _26497) = (term246 _26486 _26497).
Proof. exact (MK_COMB (@lem1124824 _26486 _26497) (@lem1124832 _26486 _26497)). Qed.
Lemma lem1124834 {_26486 _26497 : Type'} : term246 _26486 _26497.
Proof. exact (EQ_MP (@lem1124833 _26486 _26497) (@lem1124814 _26486 _26497)). Qed.
Lemma lem1124835 {_26486 _26497 : Type'} : (term185 _26486 _26497) = (term245 _26486 _26497).
Proof. exact (@lem1124834 _26486 _26497 (@lem1124810 _26486 _26497)). Qed.
Lemma lem1124837 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term247 _3571 _3575 t)) = (term248 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1124838 {_26486 _26497 : Type'} (s : type545 _26486 _26497) (t : type545 _26486 _26497) : (s = (term249 _26486 _26497 t)) = (term250 _26486 _26497 s t).
Proof. exact (@lem1124837 (type1402 _26486) (_26486 -> _26497) s t). Qed.
Lemma lem1124839 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (_18342 = (term251 _26486 _26497)) = (term252 _26486 _26497 _18342).
Proof. exact (@lem1124838 _26486 _26497 _18342 (term186 _26486 _26497)). Qed.
Lemma lem1124840 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term187 _26486 _26497 f) = (term90 _26486 _26497 f).
Proof. exact (eq_refl (term187 _26486 _26497 f)). Qed.
Lemma lem1124841 {_26486 _26497 : Type'} : (term251 _26486 _26497) = (term186 _26486 _26497).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1124840 _26486 _26497 f)). Qed.
Lemma lem1124842 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (@eq ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342) = (@eq ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342).
Proof. exact (eq_refl (@eq ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342)). Qed.
Lemma lem1124843 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (_18342 = (term251 _26486 _26497)) = (_18342 = (term186 _26486 _26497)).
Proof. exact (MK_COMB (@lem1124842 _26486 _26497 _18342) (@lem1124841 _26486 _26497)). Qed.
Lemma lem1124844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1124845 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term253 _26486 _26497 _18342) = (term254 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124844) (@lem1124843 _26486 _26497 _18342)). Qed.
Lemma lem1124846 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term187 _26486 _26497 f) = (term90 _26486 _26497 f).
Proof. exact (eq_refl (term187 _26486 _26497 f)). Qed.
Lemma lem1124847 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term188 _26486 _26497 _18342 f) = (term188 _26486 _26497 _18342 f).
Proof. exact (eq_refl (term188 _26486 _26497 _18342 f)). Qed.
Lemma lem1124848 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : ((_18342 f) = (term187 _26486 _26497 f)) = ((_18342 f) = (term90 _26486 _26497 f)).
Proof. exact (MK_COMB (@lem1124847 _26486 _26497 _18342 f) (@lem1124846 _26486 _26497 f)). Qed.
Lemma lem1124849 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term255 _26486 _26497 _18342) = (term256 _26486 _26497 _18342).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1124848 _26486 _26497 _18342 f)). Qed.
Lemma lem1124850 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1124851 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term252 _26486 _26497 _18342) = (term257 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124850 _26486 _26497) (@lem1124849 _26486 _26497 _18342)). Qed.
Lemma lem1124852 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : ((_18342 = (term251 _26486 _26497)) = (term252 _26486 _26497 _18342)) = ((_18342 = (term186 _26486 _26497)) = (term257 _26486 _26497 _18342)).
Proof. exact (MK_COMB (@lem1124845 _26486 _26497 _18342) (@lem1124851 _26486 _26497 _18342)). Qed.
Lemma lem1124853 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (_18342 = (term186 _26486 _26497)) = (term257 _26486 _26497 _18342).
Proof. exact (EQ_MP (@lem1124852 _26486 _26497 _18342) (@lem1124839 _26486 _26497 _18342)). Qed.
Lemma lem1124855 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term247 _3571 _3575 t)) = (term248 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1124856 {_26486 : Type'} (s : type1402 _26486) (t : type1402 _26486) : (s = (term258 _26486 t)) = (term259 _26486 s t).
Proof. exact (@lem1124855 (_26486 -> Prop) _26486 s t). Qed.
Lemma lem1124857 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : ((_18342 f) = (term136 _26486 _26497 f)) = (term260 _26486 _26497 _18342 f).
Proof. exact (@lem1124856 _26486 (_18342 f) (term90 _26486 _26497 f)). Qed.
Lemma lem1124858 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) : (term134 _26486 _26497 f x) = (term135 _26486 _26497 x f).
Proof. exact (eq_refl (term134 _26486 _26497 f x)). Qed.
Lemma lem1124859 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (term136 _26486 _26497 f) = (term90 _26486 _26497 f).
Proof. exact (fun_ext (fun x : _26486 => @lem1124858 _26486 _26497 x f)). Qed.
Lemma lem1124860 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term188 _26486 _26497 _18342 f) = (term188 _26486 _26497 _18342 f).
Proof. exact (eq_refl (term188 _26486 _26497 _18342 f)). Qed.
Lemma lem1124861 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : ((_18342 f) = (term136 _26486 _26497 f)) = ((_18342 f) = (term90 _26486 _26497 f)).
Proof. exact (MK_COMB (@lem1124860 _26486 _26497 _18342 f) (@lem1124859 _26486 _26497 f)). Qed.
Lemma lem1124862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1124863 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term261 _26486 _26497 _18342 f) = (term262 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1124862) (@lem1124861 _26486 _26497 _18342 f)). Qed.
Lemma lem1124864 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) : (term134 _26486 _26497 f x) = (term135 _26486 _26497 x f).
Proof. exact (eq_refl (term134 _26486 _26497 f x)). Qed.
Lemma lem1124865 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (x : _26486) : (term263 _26486 _26497 _18342 f x) = (term263 _26486 _26497 _18342 f x).
Proof. exact (eq_refl (term263 _26486 _26497 _18342 f x)). Qed.
Lemma lem1124866 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18342 f x) = (term134 _26486 _26497 f x)) = ((_18342 f x) = (term135 _26486 _26497 x f)).
Proof. exact (MK_COMB (@lem1124865 _26486 _26497 _18342 f x) (@lem1124864 _26486 _26497 x f)). Qed.
Lemma lem1124867 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term264 _26486 _26497 _18342 f) = (term265 _26486 _26497 _18342 f).
Proof. exact (fun_ext (fun x : _26486 => @lem1124866 _26486 _26497 _18342 x f)). Qed.
Lemma lem1124868 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124869 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term260 _26486 _26497 _18342 f) = (term266 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1124868 _26486) (@lem1124867 _26486 _26497 _18342 f)). Qed.
Lemma lem1124870 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (((_18342 f) = (term136 _26486 _26497 f)) = (term260 _26486 _26497 _18342 f)) = (((_18342 f) = (term90 _26486 _26497 f)) = (term266 _26486 _26497 _18342 f)).
Proof. exact (MK_COMB (@lem1124863 _26486 _26497 _18342 f) (@lem1124869 _26486 _26497 _18342 f)). Qed.
Lemma lem1124871 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : ((_18342 f) = (term90 _26486 _26497 f)) = (term266 _26486 _26497 _18342 f).
Proof. exact (EQ_MP (@lem1124870 _26486 _26497 _18342 f) (@lem1124857 _26486 _26497 _18342 f)). Qed.
Lemma lem1124872 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18342 f x) = (term135 _26486 _26497 x f)) = ((_18342 f x) = (term135 _26486 _26497 x f)).
Proof. exact (eq_refl ((_18342 f x) = (term135 _26486 _26497 x f))). Qed.
Lemma lem1124873 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term265 _26486 _26497 _18342 f) = (term265 _26486 _26497 _18342 f).
Proof. exact (fun_ext (fun x : _26486 => @lem1124872 _26486 _26497 _18342 x f)). Qed.
Lemma lem1124874 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1124875 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term266 _26486 _26497 _18342 f) = (term266 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1124874 _26486) (@lem1124873 _26486 _26497 _18342 f)). Qed.
Lemma lem1124876 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : ((_18342 f) = (term90 _26486 _26497 f)) = (term266 _26486 _26497 _18342 f).
Proof. exact (TRANS (@lem1124871 _26486 _26497 _18342 f) (@lem1124875 _26486 _26497 _18342 f)). Qed.
Lemma lem1124877 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term256 _26486 _26497 _18342) = (term267 _26486 _26497 _18342).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1124876 _26486 _26497 _18342 f)). Qed.
Lemma lem1124878 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1124879 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term257 _26486 _26497 _18342) = (term268 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124878 _26486 _26497) (@lem1124877 _26486 _26497 _18342)). Qed.
Lemma lem1124880 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (_18342 = (term186 _26486 _26497)) = (term268 _26486 _26497 _18342).
Proof. exact (TRANS (@lem1124853 _26486 _26497 _18342) (@lem1124879 _26486 _26497 _18342)). Qed.
Lemma lem1124881 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1124882 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term233 _26486 _26497 _18342) = (term269 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124881) (@lem1124880 _26486 _26497 _18342)). Qed.
Lemma lem1124883 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term224 _26486 _26497 _18342) = (term224 _26486 _26497 _18342).
Proof. exact (eq_refl (term224 _26486 _26497 _18342)). Qed.
Lemma lem1124884 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term241 _26486 _26497 _18342) = (term270 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1124882 _26486 _26497 _18342) (@lem1124883 _26486 _26497 _18342)). Qed.
Lemma lem1124885 {_26486 _26497 : Type'} : (term243 _26486 _26497) = (term271 _26486 _26497).
Proof. exact (fun_ext (fun _18342 : type545 _26486 _26497 => @lem1124884 _26486 _26497 _18342)). Qed.
Lemma lem1124886 {_26486 _26497 : Type'} : (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)) = (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)).
Proof. exact (eq_refl (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop))). Qed.
Lemma lem1124887 {_26486 _26497 : Type'} : (term245 _26486 _26497) = (term272 _26486 _26497).
Proof. exact (MK_COMB (@lem1124886 _26486 _26497) (@lem1124885 _26486 _26497)). Qed.
Lemma lem1124888 {_26486 _26497 : Type'} : (term232 _26486 _26497) = (term232 _26486 _26497).
Proof. exact (eq_refl (term232 _26486 _26497)). Qed.
Lemma lem1124889 {_26486 _26497 : Type'} : ((term185 _26486 _26497) = (term245 _26486 _26497)) = ((term185 _26486 _26497) = (term272 _26486 _26497)).
Proof. exact (MK_COMB (@lem1124888 _26486 _26497) (@lem1124887 _26486 _26497)). Qed.
Lemma lem1124890 {_26486 _26497 : Type'} : (term185 _26486 _26497) = (term272 _26486 _26497).
Proof. exact (EQ_MP (@lem1124889 _26486 _26497) (@lem1124835 _26486 _26497)). Qed.
Lemma lem1124891 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : _18343 = (term273 _26486 _26497).
Proof. exact (h1). Qed.
Lemma lem1124892 {_26486 : Type'} (x : _26486) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1124893 {_26486 _26497 : Type'} (x : _26486) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (_18343 x) = (term274 _26486 _26497 x).
Proof. exact (MK_COMB (@lem1124891 _26486 _26497 _18343 h1) (@lem1124892 _26486 x)). Qed.
Lemma lem1124894 {_26486 _26497 : Type'} (x : _26486) : (term274 _26486 _26497 x) = (term275 _26486 _26497 x).
Proof. exact (eq_refl (term274 _26486 _26497 x)). Qed.
Lemma lem1124895 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term276 _26486 _26497 _18343 x) = (term276 _26486 _26497 _18343 x).
Proof. exact (eq_refl (term276 _26486 _26497 _18343 x)). Qed.
Lemma lem1124896 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : ((_18343 x) = (term274 _26486 _26497 x)) = ((_18343 x) = (term275 _26486 _26497 x)).
Proof. exact (MK_COMB (@lem1124895 _26486 _26497 _18343 x) (@lem1124894 _26486 _26497 x)). Qed.
Lemma lem1124897 {_26486 _26497 : Type'} (x : _26486) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (_18343 x) = (term275 _26486 _26497 x).
Proof. exact (EQ_MP (@lem1124896 _26486 _26497 _18343 x) (@lem1124893 _26486 _26497 x _18343 h1)). Qed.
Lemma lem1124898 {_26486 _26497 : Type'} (f : _26486 -> _26497) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1124899 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (_18343 x f) = (term277 _26486 _26497 x f).
Proof. exact (MK_COMB (@lem1124897 _26486 _26497 x _18343 h1) (@lem1124898 _26486 _26497 f)). Qed.
Lemma lem1124900 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) : (term277 _26486 _26497 x f) = (term135 _26486 _26497 x f).
Proof. exact (eq_refl (term277 _26486 _26497 x f)). Qed.
Lemma lem1124901 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term278 _26486 _26497 _18343 x f) = (term278 _26486 _26497 _18343 x f).
Proof. exact (eq_refl (term278 _26486 _26497 _18343 x f)). Qed.
Lemma lem1124902 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18343 x f) = (term277 _26486 _26497 x f)) = ((_18343 x f) = (term135 _26486 _26497 x f)).
Proof. exact (MK_COMB (@lem1124901 _26486 _26497 _18343 x f) (@lem1124900 _26486 _26497 x f)). Qed.
Lemma lem1124903 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (_18343 x f) = (term135 _26486 _26497 x f).
Proof. exact (EQ_MP (@lem1124902 _26486 _26497 _18343 x f) (@lem1124899 _26486 _26497 x f _18343 h1)). Qed.
Lemma lem1124989 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term205 _26486 _26497 _18342 h h' t f t') = (term205 _26486 _26497 _18342 h h' t f t').
Proof. exact (eq_refl (term205 _26486 _26497 _18342 h h' t f t')). Qed.
Lemma lem1125014 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : (term209 _26486 _26497 _18342 t f m) = (term209 _26486 _26497 _18342 t f m).
Proof. exact (eq_refl (term209 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1125015 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term211 _26486 _26497 _18342 t f) = (term211 _26486 _26497 _18342 t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1125014 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1125016 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1125017 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term212 _26486 _26497 _18342 t f) = (term212 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1125016 _26486) (@lem1125015 _26486 _26497 _18342 t f)). Qed.
Lemma lem1125018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1125019 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term213 _26486 _26497 _18342 t f) = (term213 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1125018) (@lem1125017 _26486 _26497 _18342 t f)). Qed.
Lemma lem1125020 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term214 _26486 _26497 _18342 h h' t f t') = (term214 _26486 _26497 _18342 h h' t f t').
Proof. exact (MK_COMB (@lem1125019 _26486 _26497 _18342 t f) (@lem1124989 _26486 _26497 _18342 h h' t f t')). Qed.
Lemma lem1125021 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term215 _26486 _26497 _18342 h' t f t') = (term215 _26486 _26497 _18342 h' t f t').
Proof. exact (fun_ext (fun h : _26486 => @lem1125020 _26486 _26497 _18342 h h' t f t')). Qed.
Lemma lem1125022 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125023 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term216 _26486 _26497 _18342 h' t f t') = (term216 _26486 _26497 _18342 h' t f t').
Proof. exact (MK_COMB (@lem1125022 _26486) (@lem1125021 _26486 _26497 _18342 h' t f t')). Qed.
Lemma lem1125024 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term217 _26486 _26497 _18342 t f t') = (term217 _26486 _26497 _18342 t f t').
Proof. exact (fun_ext (fun h' : _26486 => @lem1125023 _26486 _26497 _18342 h' t f t')). Qed.
Lemma lem1125025 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125026 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term218 _26486 _26497 _18342 t f t') = (term218 _26486 _26497 _18342 t f t').
Proof. exact (MK_COMB (@lem1125025 _26486) (@lem1125024 _26486 _26497 _18342 t f t')). Qed.
Lemma lem1125027 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t' : list _26486) : (term219 _26486 _26497 _18342 f t') = (term219 _26486 _26497 _18342 f t').
Proof. exact (fun_ext (fun t : list _26486 => @lem1125026 _26486 _26497 _18342 t f t')). Qed.
Lemma lem1125028 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1125029 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t' : list _26486) : (term220 _26486 _26497 _18342 f t') = (term220 _26486 _26497 _18342 f t').
Proof. exact (MK_COMB (@lem1125028 _26486) (@lem1125027 _26486 _26497 _18342 f t')). Qed.
Lemma lem1125030 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t' : list _26486) : (term221 _26486 _26497 _18342 t') = (term221 _26486 _26497 _18342 t').
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125029 _26486 _26497 _18342 f t')). Qed.
Lemma lem1125031 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1125032 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t' : list _26486) : (term222 _26486 _26497 _18342 t') = (term222 _26486 _26497 _18342 t').
Proof. exact (MK_COMB (@lem1125031 _26486 _26497) (@lem1125030 _26486 _26497 _18342 t')). Qed.
Lemma lem1125033 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term223 _26486 _26497 _18342) = (term223 _26486 _26497 _18342).
Proof. exact (fun_ext (fun t' : list _26486 => @lem1125032 _26486 _26497 _18342 t')). Qed.
Lemma lem1125034 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1125035 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term224 _26486 _26497 _18342) = (term224 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1125034 _26486) (@lem1125033 _26486 _26497 _18342)). Qed.
Lemma lem1125037 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term135 _26486 _26497 x f) = (_18343 x f).
Proof. exact (SYM (@lem1124903 _26486 _26497 x f _18343 h1)). Qed.
Lemma lem1125038 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term135 _26486 _26497 x f) = (_18343 x f).
Proof. exact (@lem1125037 _26486 _26497 x f _18343 h1). Qed.
Lemma lem1125045 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (x : _26486) : (term263 _26486 _26497 _18342 f x) = (term263 _26486 _26497 _18342 f x).
Proof. exact (eq_refl (term263 _26486 _26497 _18342 f x)). Qed.
Lemma lem1125046 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (x : _26486) (f : _26486 -> _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : ((_18342 f x) = (term135 _26486 _26497 x f)) = ((_18342 f x) = (_18343 x f)).
Proof. exact (MK_COMB (@lem1125045 _26486 _26497 _18342 f x) (@lem1125038 _26486 _26497 x f _18343 h1)). Qed.
Lemma lem1125047 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term265 _26486 _26497 _18342 f) = (term279 _26486 _26497 _18342 _18343 f).
Proof. exact (fun_ext (fun x : _26486 => @lem1125046 _26486 _26497 _18342 x f _18343 h1)). Qed.
Lemma lem1125048 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125049 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term266 _26486 _26497 _18342 f) = (term280 _26486 _26497 _18342 _18343 f).
Proof. exact (MK_COMB (@lem1125048 _26486) (@lem1125047 _26486 _26497 _18342 f _18343 h1)). Qed.
Lemma lem1125050 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term267 _26486 _26497 _18342) = (term281 _26486 _26497 _18342 _18343).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125049 _26486 _26497 _18342 f _18343 h1)). Qed.
Lemma lem1125051 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1125052 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term268 _26486 _26497 _18342) = (term282 _26486 _26497 _18342 _18343).
Proof. exact (MK_COMB (@lem1125051 _26486 _26497) (@lem1125050 _26486 _26497 _18342 _18343 h1)). Qed.
Lemma lem1125053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1125054 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term269 _26486 _26497 _18342) = (term283 _26486 _26497 _18342 _18343).
Proof. exact (MK_COMB (@lem1125053) (@lem1125052 _26486 _26497 _18342 _18343 h1)). Qed.
Lemma lem1125055 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term270 _26486 _26497 _18342) = (term284 _26486 _26497 _18343 _18342).
Proof. exact (MK_COMB (@lem1125054 _26486 _26497 _18342 _18343 h1) (@lem1125035 _26486 _26497 _18342)). Qed.
Lemma lem1125056 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term271 _26486 _26497) = (term285 _26486 _26497 _18343).
Proof. exact (fun_ext (fun _18342 : type545 _26486 _26497 => @lem1125055 _26486 _26497 _18342 _18343 h1)). Qed.
Lemma lem1125057 {_26486 _26497 : Type'} : (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)) = (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)).
Proof. exact (eq_refl (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop))). Qed.
Lemma lem1125058 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (h1 : _18343 = (term273 _26486 _26497)) : (term272 _26486 _26497) = (term286 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125057 _26486 _26497) (@lem1125056 _26486 _26497 _18343 h1)). Qed.
Lemma lem1125059 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : term287 _26486 _26497 _18343.
Proof. exact (fun h0 : _18343 = (term273 _26486 _26497) => @lem1125058 _26486 _26497 _18343 h0). Qed.
Lemma lem1125060 {_26486 _26497 : Type'} : term288 _26486 _26497.
Proof. exact (fun _18343 : type1360 _26486 _26497 => @lem1125059 _26486 _26497 _18343). Qed.
Lemma lem1125062 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term227 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1125063 {_26486 _26497 : Type'} (P : Prop) (c : type1360 _26486 _26497) (Q : type390 _26486 _26497) : term289 _26486 _26497 P c Q.
Proof. exact (@lem1125062 (type1360 _26486 _26497) P c Q). Qed.
Lemma lem1125064 {_26486 _26497 : Type'} : term290 _26486 _26497.
Proof. exact (@lem1125063 _26486 _26497 (term272 _26486 _26497) (term273 _26486 _26497) (term291 _26486 _26497)). Qed.
Lemma lem1125065 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term292 _26486 _26497 _18343) = (term286 _26486 _26497 _18343).
Proof. exact (eq_refl (term292 _26486 _26497 _18343)). Qed.
Lemma lem1125066 {_26486 _26497 : Type'} : (term293 _26486 _26497) = (term293 _26486 _26497).
Proof. exact (eq_refl (term293 _26486 _26497)). Qed.
Lemma lem1125067 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : ((term272 _26486 _26497) = (term292 _26486 _26497 _18343)) = ((term272 _26486 _26497) = (term286 _26486 _26497 _18343)).
Proof. exact (MK_COMB (@lem1125066 _26486 _26497) (@lem1125065 _26486 _26497 _18343)). Qed.
Lemma lem1125068 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term294 _26486 _26497 _18343) = (term294 _26486 _26497 _18343).
Proof. exact (eq_refl (term294 _26486 _26497 _18343)). Qed.
Lemma lem1125069 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term295 _26486 _26497 _18343) = (term287 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125068 _26486 _26497 _18343) (@lem1125067 _26486 _26497 _18343)). Qed.
Lemma lem1125070 {_26486 _26497 : Type'} : (term296 _26486 _26497) = (term297 _26486 _26497).
Proof. exact (fun_ext (fun _18343 : type1360 _26486 _26497 => @lem1125069 _26486 _26497 _18343)). Qed.
Lemma lem1125071 {_26486 _26497 : Type'} : (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)) = (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)).
Proof. exact (eq_refl (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop))). Qed.
Lemma lem1125072 {_26486 _26497 : Type'} : (term298 _26486 _26497) = (term288 _26486 _26497).
Proof. exact (MK_COMB (@lem1125071 _26486 _26497) (@lem1125070 _26486 _26497)). Qed.
Lemma lem1125073 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1125074 {_26486 _26497 : Type'} : (term299 _26486 _26497) = (term300 _26486 _26497).
Proof. exact (MK_COMB (@lem1125073) (@lem1125072 _26486 _26497)). Qed.
Lemma lem1125075 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term292 _26486 _26497 _18343) = (term286 _26486 _26497 _18343).
Proof. exact (eq_refl (term292 _26486 _26497 _18343)). Qed.
Lemma lem1125076 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term294 _26486 _26497 _18343) = (term294 _26486 _26497 _18343).
Proof. exact (eq_refl (term294 _26486 _26497 _18343)). Qed.
Lemma lem1125077 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term301 _26486 _26497 _18343) = (term302 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125076 _26486 _26497 _18343) (@lem1125075 _26486 _26497 _18343)). Qed.
Lemma lem1125078 {_26486 _26497 : Type'} : (term303 _26486 _26497) = (term304 _26486 _26497).
Proof. exact (fun_ext (fun _18343 : type1360 _26486 _26497 => @lem1125077 _26486 _26497 _18343)). Qed.
Lemma lem1125079 {_26486 _26497 : Type'} : (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)) = (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)).
Proof. exact (eq_refl (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop))). Qed.
Lemma lem1125080 {_26486 _26497 : Type'} : (term305 _26486 _26497) = (term306 _26486 _26497).
Proof. exact (MK_COMB (@lem1125079 _26486 _26497) (@lem1125078 _26486 _26497)). Qed.
Lemma lem1125081 {_26486 _26497 : Type'} : (term293 _26486 _26497) = (term293 _26486 _26497).
Proof. exact (eq_refl (term293 _26486 _26497)). Qed.
Lemma lem1125082 {_26486 _26497 : Type'} : ((term272 _26486 _26497) = (term305 _26486 _26497)) = ((term272 _26486 _26497) = (term306 _26486 _26497)).
Proof. exact (MK_COMB (@lem1125081 _26486 _26497) (@lem1125080 _26486 _26497)). Qed.
Lemma lem1125083 {_26486 _26497 : Type'} : (term290 _26486 _26497) = (term307 _26486 _26497).
Proof. exact (MK_COMB (@lem1125074 _26486 _26497) (@lem1125082 _26486 _26497)). Qed.
Lemma lem1125084 {_26486 _26497 : Type'} : term307 _26486 _26497.
Proof. exact (EQ_MP (@lem1125083 _26486 _26497) (@lem1125064 _26486 _26497)). Qed.
Lemma lem1125085 {_26486 _26497 : Type'} : (term272 _26486 _26497) = (term306 _26486 _26497).
Proof. exact (@lem1125084 _26486 _26497 (@lem1125060 _26486 _26497)). Qed.
Lemma lem1125087 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term247 _3571 _3575 t)) = (term248 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1125088 {_26486 _26497 : Type'} (s : type1360 _26486 _26497) (t : type1360 _26486 _26497) : (s = (term308 _26486 _26497 t)) = (term309 _26486 _26497 s t).
Proof. exact (@lem1125087 (type551 _26486 _26497) _26486 s t). Qed.
Lemma lem1125089 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (_18343 = (term310 _26486 _26497)) = (term311 _26486 _26497 _18343).
Proof. exact (@lem1125088 _26486 _26497 _18343 (term273 _26486 _26497)). Qed.
Lemma lem1125090 {_26486 _26497 : Type'} (x : _26486) : (term274 _26486 _26497 x) = (term275 _26486 _26497 x).
Proof. exact (eq_refl (term274 _26486 _26497 x)). Qed.
Lemma lem1125091 {_26486 _26497 : Type'} : (term310 _26486 _26497) = (term273 _26486 _26497).
Proof. exact (fun_ext (fun x : _26486 => @lem1125090 _26486 _26497 x)). Qed.
Lemma lem1125092 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (@eq (_26486 -> (_26486 -> _26497) -> _26486 -> Prop) _18343) = (@eq (_26486 -> (_26486 -> _26497) -> _26486 -> Prop) _18343).
Proof. exact (eq_refl (@eq (_26486 -> (_26486 -> _26497) -> _26486 -> Prop) _18343)). Qed.
Lemma lem1125093 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (_18343 = (term310 _26486 _26497)) = (_18343 = (term273 _26486 _26497)).
Proof. exact (MK_COMB (@lem1125092 _26486 _26497 _18343) (@lem1125091 _26486 _26497)). Qed.
Lemma lem1125094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1125095 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term312 _26486 _26497 _18343) = (term313 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125094) (@lem1125093 _26486 _26497 _18343)). Qed.
Lemma lem1125096 {_26486 _26497 : Type'} (x : _26486) : (term274 _26486 _26497 x) = (term275 _26486 _26497 x).
Proof. exact (eq_refl (term274 _26486 _26497 x)). Qed.
Lemma lem1125097 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term276 _26486 _26497 _18343 x) = (term276 _26486 _26497 _18343 x).
Proof. exact (eq_refl (term276 _26486 _26497 _18343 x)). Qed.
Lemma lem1125098 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : ((_18343 x) = (term274 _26486 _26497 x)) = ((_18343 x) = (term275 _26486 _26497 x)).
Proof. exact (MK_COMB (@lem1125097 _26486 _26497 _18343 x) (@lem1125096 _26486 _26497 x)). Qed.
Lemma lem1125099 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term314 _26486 _26497 _18343) = (term315 _26486 _26497 _18343).
Proof. exact (fun_ext (fun x : _26486 => @lem1125098 _26486 _26497 _18343 x)). Qed.
Lemma lem1125100 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125101 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term311 _26486 _26497 _18343) = (term316 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125100 _26486) (@lem1125099 _26486 _26497 _18343)). Qed.
Lemma lem1125102 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : ((_18343 = (term310 _26486 _26497)) = (term311 _26486 _26497 _18343)) = ((_18343 = (term273 _26486 _26497)) = (term316 _26486 _26497 _18343)).
Proof. exact (MK_COMB (@lem1125095 _26486 _26497 _18343) (@lem1125101 _26486 _26497 _18343)). Qed.
Lemma lem1125103 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (_18343 = (term273 _26486 _26497)) = (term316 _26486 _26497 _18343).
Proof. exact (EQ_MP (@lem1125102 _26486 _26497 _18343) (@lem1125089 _26486 _26497 _18343)). Qed.
Lemma lem1125105 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term247 _3571 _3575 t)) = (term248 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1125106 {_26486 _26497 : Type'} (s : type551 _26486 _26497) (t : type551 _26486 _26497) : (s = (term317 _26486 _26497 t)) = (term318 _26486 _26497 s t).
Proof. exact (@lem1125105 (_26486 -> Prop) (_26486 -> _26497) s t). Qed.
Lemma lem1125107 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : ((_18343 x) = (term319 _26486 _26497 x)) = (term320 _26486 _26497 _18343 x).
Proof. exact (@lem1125106 _26486 _26497 (_18343 x) (term275 _26486 _26497 x)). Qed.
Lemma lem1125108 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) : (term277 _26486 _26497 x f) = (term135 _26486 _26497 x f).
Proof. exact (eq_refl (term277 _26486 _26497 x f)). Qed.
Lemma lem1125109 {_26486 _26497 : Type'} (x : _26486) : (term319 _26486 _26497 x) = (term275 _26486 _26497 x).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125108 _26486 _26497 x f)). Qed.
Lemma lem1125110 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term276 _26486 _26497 _18343 x) = (term276 _26486 _26497 _18343 x).
Proof. exact (eq_refl (term276 _26486 _26497 _18343 x)). Qed.
Lemma lem1125111 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : ((_18343 x) = (term319 _26486 _26497 x)) = ((_18343 x) = (term275 _26486 _26497 x)).
Proof. exact (MK_COMB (@lem1125110 _26486 _26497 _18343 x) (@lem1125109 _26486 _26497 x)). Qed.
Lemma lem1125112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1125113 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term321 _26486 _26497 _18343 x) = (term322 _26486 _26497 _18343 x).
Proof. exact (MK_COMB (@lem1125112) (@lem1125111 _26486 _26497 _18343 x)). Qed.
Lemma lem1125114 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) : (term277 _26486 _26497 x f) = (term135 _26486 _26497 x f).
Proof. exact (eq_refl (term277 _26486 _26497 x f)). Qed.
Lemma lem1125115 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term278 _26486 _26497 _18343 x f) = (term278 _26486 _26497 _18343 x f).
Proof. exact (eq_refl (term278 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125116 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18343 x f) = (term277 _26486 _26497 x f)) = ((_18343 x f) = (term135 _26486 _26497 x f)).
Proof. exact (MK_COMB (@lem1125115 _26486 _26497 _18343 x f) (@lem1125114 _26486 _26497 x f)). Qed.
Lemma lem1125117 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term323 _26486 _26497 _18343 x) = (term324 _26486 _26497 _18343 x).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125116 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125118 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1125119 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term320 _26486 _26497 _18343 x) = (term325 _26486 _26497 _18343 x).
Proof. exact (MK_COMB (@lem1125118 _26486 _26497) (@lem1125117 _26486 _26497 _18343 x)). Qed.
Lemma lem1125120 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (((_18343 x) = (term319 _26486 _26497 x)) = (term320 _26486 _26497 _18343 x)) = (((_18343 x) = (term275 _26486 _26497 x)) = (term325 _26486 _26497 _18343 x)).
Proof. exact (MK_COMB (@lem1125113 _26486 _26497 _18343 x) (@lem1125119 _26486 _26497 _18343 x)). Qed.
Lemma lem1125121 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : ((_18343 x) = (term275 _26486 _26497 x)) = (term325 _26486 _26497 _18343 x).
Proof. exact (EQ_MP (@lem1125120 _26486 _26497 _18343 x) (@lem1125107 _26486 _26497 _18343 x)). Qed.
Lemma lem1125123 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term247 _3571 _3575 t)) = (term248 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1125124 {_26486 : Type'} (s : _26486 -> Prop) (t : _26486 -> Prop) : (s = (term326 _26486 t)) = (term327 _26486 s t).
Proof. exact (@lem1125123 Prop _26486 s t). Qed.
Lemma lem1125125 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18343 x f) = (term143 _26486 _26497 x f)) = (term328 _26486 _26497 _18343 x f).
Proof. exact (@lem1125124 _26486 (_18343 x f) (term135 _26486 _26497 x f)). Qed.
Lemma lem1125126 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) (y : _26486) : (term140 _26486 _26497 x f y) = ((f x) = (f y)).
Proof. exact (eq_refl (term140 _26486 _26497 x f y)). Qed.
Lemma lem1125127 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) : (term143 _26486 _26497 x f) = (term135 _26486 _26497 x f).
Proof. exact (fun_ext (fun y : _26486 => @lem1125126 _26486 _26497 x f y)). Qed.
Lemma lem1125128 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term278 _26486 _26497 _18343 x f) = (term278 _26486 _26497 _18343 x f).
Proof. exact (eq_refl (term278 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125129 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18343 x f) = (term143 _26486 _26497 x f)) = ((_18343 x f) = (term135 _26486 _26497 x f)).
Proof. exact (MK_COMB (@lem1125128 _26486 _26497 _18343 x f) (@lem1125127 _26486 _26497 x f)). Qed.
Lemma lem1125130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1125131 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term329 _26486 _26497 _18343 x f) = (term330 _26486 _26497 _18343 x f).
Proof. exact (MK_COMB (@lem1125130) (@lem1125129 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125132 {_26486 _26497 : Type'} (x : _26486) (f : _26486 -> _26497) (y : _26486) : (term140 _26486 _26497 x f y) = ((f x) = (f y)).
Proof. exact (eq_refl (term140 _26486 _26497 x f y)). Qed.
Lemma lem1125133 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) (y : _26486) : (term331 _26486 _26497 _18343 x f y) = (term331 _26486 _26497 _18343 x f y).
Proof. exact (eq_refl (term331 _26486 _26497 _18343 x f y)). Qed.
Lemma lem1125134 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) (y : _26486) : ((_18343 x f y) = (term140 _26486 _26497 x f y)) = ((_18343 x f y) = ((f x) = (f y))).
Proof. exact (MK_COMB (@lem1125133 _26486 _26497 _18343 x f y) (@lem1125132 _26486 _26497 x f y)). Qed.
Lemma lem1125135 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term332 _26486 _26497 _18343 x f) = (term333 _26486 _26497 _18343 x f).
Proof. exact (fun_ext (fun y : _26486 => @lem1125134 _26486 _26497 _18343 x f y)). Qed.
Lemma lem1125136 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125137 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term328 _26486 _26497 _18343 x f) = (term334 _26486 _26497 _18343 x f).
Proof. exact (MK_COMB (@lem1125136 _26486) (@lem1125135 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125138 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (((_18343 x f) = (term143 _26486 _26497 x f)) = (term328 _26486 _26497 _18343 x f)) = (((_18343 x f) = (term135 _26486 _26497 x f)) = (term334 _26486 _26497 _18343 x f)).
Proof. exact (MK_COMB (@lem1125131 _26486 _26497 _18343 x f) (@lem1125137 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125139 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18343 x f) = (term135 _26486 _26497 x f)) = (term334 _26486 _26497 _18343 x f).
Proof. exact (EQ_MP (@lem1125138 _26486 _26497 _18343 x f) (@lem1125125 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125140 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) (y : _26486) : ((_18343 x f y) = ((f x) = (f y))) = ((_18343 x f y) = ((f x) = (f y))).
Proof. exact (eq_refl ((_18343 x f y) = ((f x) = (f y)))). Qed.
Lemma lem1125141 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term333 _26486 _26497 _18343 x f) = (term333 _26486 _26497 _18343 x f).
Proof. exact (fun_ext (fun y : _26486 => @lem1125140 _26486 _26497 _18343 x f y)). Qed.
Lemma lem1125142 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125143 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term334 _26486 _26497 _18343 x f) = (term334 _26486 _26497 _18343 x f).
Proof. exact (MK_COMB (@lem1125142 _26486) (@lem1125141 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125144 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18343 x f) = (term135 _26486 _26497 x f)) = (term334 _26486 _26497 _18343 x f).
Proof. exact (TRANS (@lem1125139 _26486 _26497 _18343 x f) (@lem1125143 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125145 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term324 _26486 _26497 _18343 x) = (term335 _26486 _26497 _18343 x).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125144 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125146 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1125147 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term325 _26486 _26497 _18343 x) = (term336 _26486 _26497 _18343 x).
Proof. exact (MK_COMB (@lem1125146 _26486 _26497) (@lem1125145 _26486 _26497 _18343 x)). Qed.
Lemma lem1125148 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : ((_18343 x) = (term275 _26486 _26497 x)) = (term336 _26486 _26497 _18343 x).
Proof. exact (TRANS (@lem1125121 _26486 _26497 _18343 x) (@lem1125147 _26486 _26497 _18343 x)). Qed.
Lemma lem1125149 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term315 _26486 _26497 _18343) = (term337 _26486 _26497 _18343).
Proof. exact (fun_ext (fun x : _26486 => @lem1125148 _26486 _26497 _18343 x)). Qed.
Lemma lem1125150 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125151 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term316 _26486 _26497 _18343) = (term338 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125150 _26486) (@lem1125149 _26486 _26497 _18343)). Qed.
Lemma lem1125152 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (_18343 = (term273 _26486 _26497)) = (term338 _26486 _26497 _18343).
Proof. exact (TRANS (@lem1125103 _26486 _26497 _18343) (@lem1125151 _26486 _26497 _18343)). Qed.
Lemma lem1125153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1125154 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term294 _26486 _26497 _18343) = (term339 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125153) (@lem1125152 _26486 _26497 _18343)). Qed.
Lemma lem1125155 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term286 _26486 _26497 _18343) = (term286 _26486 _26497 _18343).
Proof. exact (eq_refl (term286 _26486 _26497 _18343)). Qed.
Lemma lem1125156 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term302 _26486 _26497 _18343) = (term340 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125154 _26486 _26497 _18343) (@lem1125155 _26486 _26497 _18343)). Qed.
Lemma lem1125157 {_26486 _26497 : Type'} : (term304 _26486 _26497) = (term341 _26486 _26497).
Proof. exact (fun_ext (fun _18343 : type1360 _26486 _26497 => @lem1125156 _26486 _26497 _18343)). Qed.
Lemma lem1125158 {_26486 _26497 : Type'} : (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)) = (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)).
Proof. exact (eq_refl (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop))). Qed.
Lemma lem1125159 {_26486 _26497 : Type'} : (term306 _26486 _26497) = (term342 _26486 _26497).
Proof. exact (MK_COMB (@lem1125158 _26486 _26497) (@lem1125157 _26486 _26497)). Qed.
Lemma lem1125160 {_26486 _26497 : Type'} : (term293 _26486 _26497) = (term293 _26486 _26497).
Proof. exact (eq_refl (term293 _26486 _26497)). Qed.
Lemma lem1125161 {_26486 _26497 : Type'} : ((term272 _26486 _26497) = (term306 _26486 _26497)) = ((term272 _26486 _26497) = (term342 _26486 _26497)).
Proof. exact (MK_COMB (@lem1125160 _26486 _26497) (@lem1125159 _26486 _26497)). Qed.
Lemma lem1125164 {_26486 _26497 : Type'} : (term272 _26486 _26497) = (term342 _26486 _26497).
Proof. exact (EQ_MP (@lem1125161 _26486 _26497) (@lem1125085 _26486 _26497)). Qed.
Lemma lem1125165 {_26486 _26497 : Type'} : (term185 _26486 _26497) = (term342 _26486 _26497).
Proof. exact (TRANS (@lem1124890 _26486 _26497) (@lem1125164 _26486 _26497)). Qed.
Lemma lem1125166 {_26486 _26497 : Type'} : (term184 _26486 _26497) = (term342 _26486 _26497).
Proof. exact (TRANS (@lem1124669 _26486 _26497) (@lem1125165 _26486 _26497)). Qed.
Lemma lem1125187 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term205 _26486 _26497 _18342 h h' t f t') = (term205 _26486 _26497 _18342 h h' t f t').
Proof. exact (eq_refl (term205 _26486 _26497 _18342 h h' t f t')). Qed.
Lemma lem1125192 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : (term209 _26486 _26497 _18342 t f m) = (term209 _26486 _26497 _18342 t f m).
Proof. exact (eq_refl (term209 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1125193 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term211 _26486 _26497 _18342 t f) = (term211 _26486 _26497 _18342 t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1125192 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1125194 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1125195 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term212 _26486 _26497 _18342 t f) = (term212 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1125194 _26486) (@lem1125193 _26486 _26497 _18342 t f)). Qed.
Lemma lem1125196 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1125197 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term213 _26486 _26497 _18342 t f) = (term213 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1125196) (@lem1125195 _26486 _26497 _18342 t f)). Qed.
Lemma lem1125198 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term214 _26486 _26497 _18342 h h' t f t') = (term214 _26486 _26497 _18342 h h' t f t').
Proof. exact (MK_COMB (@lem1125197 _26486 _26497 _18342 t f) (@lem1125187 _26486 _26497 _18342 h h' t f t')). Qed.
Lemma lem1125199 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term215 _26486 _26497 _18342 h' t f t') = (term215 _26486 _26497 _18342 h' t f t').
Proof. exact (fun_ext (fun h : _26486 => @lem1125198 _26486 _26497 _18342 h h' t f t')). Qed.
Lemma lem1125200 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125201 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term216 _26486 _26497 _18342 h' t f t') = (term216 _26486 _26497 _18342 h' t f t').
Proof. exact (MK_COMB (@lem1125200 _26486) (@lem1125199 _26486 _26497 _18342 h' t f t')). Qed.
Lemma lem1125202 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term217 _26486 _26497 _18342 t f t') = (term217 _26486 _26497 _18342 t f t').
Proof. exact (fun_ext (fun h' : _26486 => @lem1125201 _26486 _26497 _18342 h' t f t')). Qed.
Lemma lem1125203 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125204 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term218 _26486 _26497 _18342 t f t') = (term218 _26486 _26497 _18342 t f t').
Proof. exact (MK_COMB (@lem1125203 _26486) (@lem1125202 _26486 _26497 _18342 t f t')). Qed.
Lemma lem1125205 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t' : list _26486) : (term219 _26486 _26497 _18342 f t') = (term219 _26486 _26497 _18342 f t').
Proof. exact (fun_ext (fun t : list _26486 => @lem1125204 _26486 _26497 _18342 t f t')). Qed.
Lemma lem1125206 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1125207 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t' : list _26486) : (term220 _26486 _26497 _18342 f t') = (term220 _26486 _26497 _18342 f t').
Proof. exact (MK_COMB (@lem1125206 _26486) (@lem1125205 _26486 _26497 _18342 f t')). Qed.
Lemma lem1125208 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t' : list _26486) : (term221 _26486 _26497 _18342 t') = (term221 _26486 _26497 _18342 t').
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125207 _26486 _26497 _18342 f t')). Qed.
Lemma lem1125209 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1125210 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t' : list _26486) : (term222 _26486 _26497 _18342 t') = (term222 _26486 _26497 _18342 t').
Proof. exact (MK_COMB (@lem1125209 _26486 _26497) (@lem1125208 _26486 _26497 _18342 t')). Qed.
Lemma lem1125211 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term223 _26486 _26497 _18342) = (term223 _26486 _26497 _18342).
Proof. exact (fun_ext (fun t' : list _26486 => @lem1125210 _26486 _26497 _18342 t')). Qed.
Lemma lem1125212 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1125213 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : (term224 _26486 _26497 _18342) = (term224 _26486 _26497 _18342).
Proof. exact (MK_COMB (@lem1125212 _26486) (@lem1125211 _26486 _26497 _18342)). Qed.
Lemma lem1125214 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : ((_18342 f x) = (_18343 x f)) = ((_18342 f x) = (_18343 x f)).
Proof. exact (eq_refl ((_18342 f x) = (_18343 x f))). Qed.
Lemma lem1125215 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) (f : _26486 -> _26497) : (term279 _26486 _26497 _18342 _18343 f) = (term279 _26486 _26497 _18342 _18343 f).
Proof. exact (fun_ext (fun x : _26486 => @lem1125214 _26486 _26497 _18342 _18343 x f)). Qed.
Lemma lem1125216 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125217 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) (f : _26486 -> _26497) : (term280 _26486 _26497 _18342 _18343 f) = (term280 _26486 _26497 _18342 _18343 f).
Proof. exact (MK_COMB (@lem1125216 _26486) (@lem1125215 _26486 _26497 _18342 _18343 f)). Qed.
Lemma lem1125218 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) : (term281 _26486 _26497 _18342 _18343) = (term281 _26486 _26497 _18342 _18343).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125217 _26486 _26497 _18342 _18343 f)). Qed.
Lemma lem1125219 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1125220 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) : (term282 _26486 _26497 _18342 _18343) = (term282 _26486 _26497 _18342 _18343).
Proof. exact (MK_COMB (@lem1125219 _26486 _26497) (@lem1125218 _26486 _26497 _18342 _18343)). Qed.
Lemma lem1125221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1125222 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (_18343 : type1360 _26486 _26497) : (term283 _26486 _26497 _18342 _18343) = (term283 _26486 _26497 _18342 _18343).
Proof. exact (MK_COMB (@lem1125221) (@lem1125220 _26486 _26497 _18342 _18343)). Qed.
Lemma lem1125223 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (_18342 : type545 _26486 _26497) : (term284 _26486 _26497 _18343 _18342) = (term284 _26486 _26497 _18343 _18342).
Proof. exact (MK_COMB (@lem1125222 _26486 _26497 _18342 _18343) (@lem1125213 _26486 _26497 _18342)). Qed.
Lemma lem1125224 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term285 _26486 _26497 _18343) = (term285 _26486 _26497 _18343).
Proof. exact (fun_ext (fun _18342 : type545 _26486 _26497 => @lem1125223 _26486 _26497 _18343 _18342)). Qed.
Lemma lem1125225 {_26486 _26497 : Type'} : (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)) = (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop)).
Proof. exact (eq_refl (@all ((_26486 -> _26497) -> _26486 -> _26486 -> Prop))). Qed.
Lemma lem1125226 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term286 _26486 _26497 _18343) = (term286 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125225 _26486 _26497) (@lem1125224 _26486 _26497 _18343)). Qed.
Lemma lem1125231 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) (y : _26486) : ((_18343 x f y) = ((f x) = (f y))) = ((_18343 x f y) = ((f x) = (f y))).
Proof. exact (eq_refl ((_18343 x f y) = ((f x) = (f y)))). Qed.
Lemma lem1125232 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term333 _26486 _26497 _18343 x f) = (term333 _26486 _26497 _18343 x f).
Proof. exact (fun_ext (fun y : _26486 => @lem1125231 _26486 _26497 _18343 x f y)). Qed.
Lemma lem1125233 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125234 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) (f : _26486 -> _26497) : (term334 _26486 _26497 _18343 x f) = (term334 _26486 _26497 _18343 x f).
Proof. exact (MK_COMB (@lem1125233 _26486) (@lem1125232 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125235 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term335 _26486 _26497 _18343 x) = (term335 _26486 _26497 _18343 x).
Proof. exact (fun_ext (fun f : _26486 -> _26497 => @lem1125234 _26486 _26497 _18343 x f)). Qed.
Lemma lem1125236 {_26486 _26497 : Type'} : (@all (_26486 -> _26497)) = (@all (_26486 -> _26497)).
Proof. exact (eq_refl (@all (_26486 -> _26497))). Qed.
Lemma lem1125237 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (x : _26486) : (term336 _26486 _26497 _18343 x) = (term336 _26486 _26497 _18343 x).
Proof. exact (MK_COMB (@lem1125236 _26486 _26497) (@lem1125235 _26486 _26497 _18343 x)). Qed.
Lemma lem1125238 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term337 _26486 _26497 _18343) = (term337 _26486 _26497 _18343).
Proof. exact (fun_ext (fun x : _26486 => @lem1125237 _26486 _26497 _18343 x)). Qed.
Lemma lem1125239 {_26486 : Type'} : (@all _26486) = (@all _26486).
Proof. exact (eq_refl (@all _26486)). Qed.
Lemma lem1125240 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term338 _26486 _26497 _18343) = (term338 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125239 _26486) (@lem1125238 _26486 _26497 _18343)). Qed.
Lemma lem1125241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1125242 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term339 _26486 _26497 _18343) = (term339 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125241) (@lem1125240 _26486 _26497 _18343)). Qed.
Lemma lem1125243 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : (term340 _26486 _26497 _18343) = (term340 _26486 _26497 _18343).
Proof. exact (MK_COMB (@lem1125242 _26486 _26497 _18343) (@lem1125226 _26486 _26497 _18343)). Qed.
Lemma lem1125244 {_26486 _26497 : Type'} : (term341 _26486 _26497) = (term341 _26486 _26497).
Proof. exact (fun_ext (fun _18343 : type1360 _26486 _26497 => @lem1125243 _26486 _26497 _18343)). Qed.
Lemma lem1125245 {_26486 _26497 : Type'} : (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)) = (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop)).
Proof. exact (eq_refl (@all (_26486 -> (_26486 -> _26497) -> _26486 -> Prop))). Qed.
Lemma lem1125246 {_26486 _26497 : Type'} : (term342 _26486 _26497) = (term342 _26486 _26497).
Proof. exact (MK_COMB (@lem1125245 _26486 _26497) (@lem1125244 _26486 _26497)). Qed.
Lemma lem1125345 {_26486 _26497 : Type'} : (term184 _26486 _26497) = (term342 _26486 _26497).
Proof. exact (TRANS (@lem1125166 _26486 _26497) (@lem1125246 _26486 _26497)). Qed.
Lemma lem1125346 {_26486 _26497 : Type'} : (term342 _26486 _26497) = (term184 _26486 _26497).
Proof. exact (SYM (@lem1125345 _26486 _26497)). Qed.
Lemma lem1125349 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term212 _26486 _26497 _18342 t f.
Proof. exact (h1). Qed.
Lemma lem1125350 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term203 _26486 _26497 _18342 h t f t') : term203 _26486 _26497 _18342 h t f t'.
Proof. exact (h1). Qed.
Lemma lem1125353 (p : Prop) : p = (term154 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1125354 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term152 _26486 _26497 h h' t f t') = (term343 _26486 _26497 h h' t f t').
Proof. exact (@lem1125353 (term152 _26486 _26497 h h' t f t')). Qed.
Lemma lem1125355 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term343 _26486 _26497 h h' t f t') = (term152 _26486 _26497 h h' t f t').
Proof. exact (SYM (@lem1125354 _26486 _26497 h h' t f t')). Qed.
Lemma lem1125356 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term344 _26486 _26497 h h' t f t') : term344 _26486 _26497 h h' t f t'.
Proof. exact (h1). Qed.
Lemma lem1125820 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : (term209 _26486 _26497 _18342 t f m) = (term345 _26486 _26497 _18342 t f m).
Proof. exact (@lem17265 (term193 _26486 _26497 _18342 f t m) ((@List.map _26486 _26497 f t) = (@List.map _26486 _26497 f m))). Qed.
Lemma lem1125821 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term211 _26486 _26497 _18342 t f) = (term346 _26486 _26497 _18342 t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1125820 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1125822 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1125875 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term212 _26486 _26497 _18342 t f) = (term347 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1125822 _26486) (@lem1125821 _26486 _26497 _18342 t f)). Qed.
Lemma lem1125876 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term347 _26486 _26497 _18342 t f.
Proof. exact (EQ_MP (@lem1125875 _26486 _26497 _18342 t f) (@lem1125349 _26486 _26497 _18342 t f h1)). Qed.
Lemma lem1125887 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term203 _26486 _26497 _18342 h t f t') = (term348 _26486 _26497 _18342 h t f t').
Proof. exact (@lem17265 (term200 _26486 _26497 _18342 f h t t') ((term100 _26486 _26497 f h t) = (@List.map _26486 _26497 f t'))). Qed.
Lemma lem1125888 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term203 _26486 _26497 _18342 h t f t') : term348 _26486 _26497 _18342 h t f t'.
Proof. exact (EQ_MP (@lem1125887 _26486 _26497 _18342 h t f t') (@lem1125350 _26486 _26497 _18342 h t f t' h1)). Qed.
Lemma lem1125898 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term194 _26486 _26497 h h' _18342 f t t'.
Proof. exact (h1). Qed.
Lemma lem1125909 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term344 _26486 _26497 h h' t f t') = (term349 _26486 _26497 h h' t f t').
Proof. exact (@lem17045 ((f h) = (f h')) ((@List.map _26486 _26497 f t) = (@List.map _26486 _26497 f t'))). Qed.
Lemma lem1125910 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term344 _26486 _26497 h h' t f t') : term349 _26486 _26497 h h' t f t'.
Proof. exact (EQ_MP (@lem1125909 _26486 _26497 h h' t f t') (@lem1125356 _26486 _26497 h h' t f t' h1)). Qed.
Lemma lem1126075 {_26497 : Type'} : (@eq (list _26497)) = (@eq (list _26497)).
Proof. exact (eq_refl (@eq (list _26497))). Qed.
Lemma lem1126082 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126083 {_26486 _26497 : Type'} (f : type540 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) f x).
Proof. exact (@lem1126082 (_26486 -> _26497) (type1139 _26486 _26497) f x). Qed.
Lemma lem1126084 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f).
Proof. exact (@lem1126083 _26486 _26497 (@List.map _26486 _26497) f). Qed.
Lemma lem1126085 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126086 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (@List.map _26486 _26497 f t) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t).
Proof. exact (MK_COMB (@lem1126084 _26486 _26497 f) (@lem1126085 _26486 t)). Qed.
Lemma lem1126088 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126089 {_26486 _26497 : Type'} (f : type1139 _26486 _26497) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26497) f x).
Proof. exact (@lem1126088 (list _26486) (list _26497) f x). Qed.
Lemma lem1126090 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t) = (term350 _26486 _26497 f t).
Proof. exact (@lem1126089 _26486 _26497 (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f) t). Qed.
Lemma lem1126092 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (@List.map _26486 _26497 f t) = (term350 _26486 _26497 f t).
Proof. exact (TRANS (@lem1126086 _26486 _26497 f t) (@lem1126090 _26486 _26497 f t)). Qed.
Lemma lem1126099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126100 {_26486 _26497 : Type'} (f : type540 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) f x).
Proof. exact (@lem1126099 (_26486 -> _26497) (type1139 _26486 _26497) f x). Qed.
Lemma lem1126101 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f).
Proof. exact (@lem1126100 _26486 _26497 (@List.map _26486 _26497) f). Qed.
Lemma lem1126102 {_26486 : Type'} (m : list _26486) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1126103 {_26486 _26497 : Type'} (f : _26486 -> _26497) (m : list _26486) : (@List.map _26486 _26497 f m) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f m).
Proof. exact (MK_COMB (@lem1126101 _26486 _26497 f) (@lem1126102 _26486 m)). Qed.
Lemma lem1126105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126106 {_26486 _26497 : Type'} (f : type1139 _26486 _26497) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26497) f x).
Proof. exact (@lem1126105 (list _26486) (list _26497) f x). Qed.
Lemma lem1126107 {_26486 _26497 : Type'} (f : _26486 -> _26497) (m : list _26486) : (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f m) = (term350 _26486 _26497 f m).
Proof. exact (@lem1126106 _26486 _26497 (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f) m). Qed.
Lemma lem1126109 {_26486 _26497 : Type'} (f : _26486 -> _26497) (m : list _26486) : (@List.map _26486 _26497 f m) = (term350 _26486 _26497 f m).
Proof. exact (TRANS (@lem1126103 _26486 _26497 f m) (@lem1126107 _26486 _26497 f m)). Qed.
Lemma lem1126110 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (term351 _26486 _26497 f t) = (term352 _26486 _26497 f t).
Proof. exact (MK_COMB (@lem1126075 _26497) (@lem1126092 _26486 _26497 f t)). Qed.
Lemma lem1126111 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : ((@List.map _26486 _26497 f t) = (@List.map _26486 _26497 f m)) = ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f m)).
Proof. exact (MK_COMB (@lem1126110 _26486 _26497 f t) (@lem1126109 _26486 _26497 f m)). Qed.
Lemma lem1126112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1126113 {_26486 : Type'} : (@ALL2 _26486 _26486) = (@ALL2 _26486 _26486).
Proof. exact (eq_refl (@ALL2 _26486 _26486)). Qed.
Lemma lem1126118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126119 {_26486 _26497 : Type'} (f : type545 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) f x).
Proof. exact (@lem1126118 (_26486 -> _26497) (type1402 _26486) f x). Qed.
Lemma lem1126121 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (_18342 f) = (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342 f).
Proof. exact (@lem1126119 _26486 _26497 _18342 f). Qed.
Lemma lem1126122 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126123 {_26486 : Type'} (m : list _26486) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1126124 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term190 _26486 _26497 _18342 f) = (term353 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1126113 _26486) (@lem1126121 _26486 _26497 _18342 f)). Qed.
Lemma lem1126125 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term192 _26486 _26497 _18342 f t) = (term354 _26486 _26497 _18342 f t).
Proof. exact (MK_COMB (@lem1126124 _26486 _26497 _18342 f) (@lem1126122 _26486 t)). Qed.
Lemma lem1126126 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (m : list _26486) : (term193 _26486 _26497 _18342 f t m) = (term355 _26486 _26497 _18342 f t m).
Proof. exact (MK_COMB (@lem1126125 _26486 _26497 _18342 f t) (@lem1126123 _26486 m)). Qed.
Lemma lem1126128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126129 {_26486 : Type'} (f : type415 _26486) (x : type1402 _26486) : (f x) = (@I ((_26486 -> _26486 -> Prop) -> (list _26486) -> (list _26486) -> Prop) f x).
Proof. exact (@lem1126128 (type1402 _26486) (type1133 _26486) f x). Qed.
Lemma lem1126130 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term353 _26486 _26497 _18342 f) = (term356 _26486 _26497 _18342 f).
Proof. exact (@lem1126129 _26486 (@ALL2 _26486 _26486) (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342 f)). Qed.
Lemma lem1126131 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126132 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term354 _26486 _26497 _18342 f t) = (term357 _26486 _26497 _18342 f t).
Proof. exact (MK_COMB (@lem1126130 _26486 _26497 _18342 f) (@lem1126131 _26486 t)). Qed.
Lemma lem1126134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126135 {_26486 : Type'} (f : type1133 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> (list _26486) -> Prop) f x).
Proof. exact (@lem1126134 (list _26486) (type1143 _26486) f x). Qed.
Lemma lem1126136 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term357 _26486 _26497 _18342 f t) = (term358 _26486 _26497 _18342 f t).
Proof. exact (@lem1126135 _26486 (term356 _26486 _26497 _18342 f) t). Qed.
Lemma lem1126137 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term354 _26486 _26497 _18342 f t) = (term358 _26486 _26497 _18342 f t).
Proof. exact (TRANS (@lem1126132 _26486 _26497 _18342 f t) (@lem1126136 _26486 _26497 _18342 f t)). Qed.
Lemma lem1126138 {_26486 : Type'} (m : list _26486) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1126139 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (m : list _26486) : (term355 _26486 _26497 _18342 f t m) = (term359 _26486 _26497 _18342 f t m).
Proof. exact (MK_COMB (@lem1126137 _26486 _26497 _18342 f t) (@lem1126138 _26486 m)). Qed.
Lemma lem1126141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126142 {_26486 : Type'} (f : type1143 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> Prop) f x).
Proof. exact (@lem1126141 (list _26486) Prop f x). Qed.
Lemma lem1126143 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (m : list _26486) : (term359 _26486 _26497 _18342 f t m) = (term360 _26486 _26497 _18342 f t m).
Proof. exact (@lem1126142 _26486 (term358 _26486 _26497 _18342 f t) m). Qed.
Lemma lem1126144 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (m : list _26486) : (term355 _26486 _26497 _18342 f t m) = (term360 _26486 _26497 _18342 f t m).
Proof. exact (TRANS (@lem1126139 _26486 _26497 _18342 f t m) (@lem1126143 _26486 _26497 _18342 f t m)). Qed.
Lemma lem1126145 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (m : list _26486) : (term193 _26486 _26497 _18342 f t m) = (term360 _26486 _26497 _18342 f t m).
Proof. exact (TRANS (@lem1126126 _26486 _26497 _18342 f t m) (@lem1126144 _26486 _26497 _18342 f t m)). Qed.
Lemma lem1126146 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (m : list _26486) : (term361 _26486 _26497 _18342 f t m) = (term362 _26486 _26497 _18342 f t m).
Proof. exact (MK_COMB (@lem1126112) (@lem1126145 _26486 _26497 _18342 f t m)). Qed.
Lemma lem1126147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1126148 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (m : list _26486) : (term363 _26486 _26497 _18342 f t m) = (term364 _26486 _26497 _18342 f t m).
Proof. exact (MK_COMB (@lem1126147) (@lem1126146 _26486 _26497 _18342 f t m)). Qed.
Lemma lem1126149 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : (term345 _26486 _26497 _18342 t f m) = (term365 _26486 _26497 _18342 t f m).
Proof. exact (MK_COMB (@lem1126148 _26486 _26497 _18342 f t m) (@lem1126111 _26486 _26497 t f m)). Qed.
Lemma lem1126150 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term346 _26486 _26497 _18342 t f) = (term366 _26486 _26497 _18342 t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1126149 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1126151 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1126152 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term347 _26486 _26497 _18342 t f) = (term367 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1126151 _26486) (@lem1126150 _26486 _26497 _18342 t f)). Qed.
Lemma lem1126153 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term367 _26486 _26497 _18342 t f.
Proof. exact (EQ_MP (@lem1126152 _26486 _26497 _18342 t f) (@lem1125876 _26486 _26497 _18342 t f h1)). Qed.
Lemma lem1126154 {_26497 : Type'} : (@eq (list _26497)) = (@eq (list _26497)).
Proof. exact (eq_refl (@eq (list _26497))). Qed.
Lemma lem1126163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126164 {_26486 : Type'} (f : type1397 _26486) (x : _26486) : (f x) = (@I (_26486 -> (list _26486) -> list _26486) f x).
Proof. exact (@lem1126163 _26486 (type1138 _26486) f x). Qed.
Lemma lem1126165 {_26486 : Type'} (h : _26486) : (@cons _26486 h) = (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h).
Proof. exact (@lem1126164 _26486 (@cons _26486) h). Qed.
Lemma lem1126166 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126167 {_26486 : Type'} (h : _26486) (t : list _26486) : (@cons _26486 h t) = (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h t).
Proof. exact (MK_COMB (@lem1126165 _26486 h) (@lem1126166 _26486 t)). Qed.
Lemma lem1126169 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126170 {_26486 : Type'} (f : type1138 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26486) f x).
Proof. exact (@lem1126169 (list _26486) (list _26486) f x). Qed.
Lemma lem1126171 {_26486 : Type'} (h : _26486) (t : list _26486) : (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h t) = (term368 _26486 h t).
Proof. exact (@lem1126170 _26486 (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h) t). Qed.
Lemma lem1126173 {_26486 : Type'} (h : _26486) (t : list _26486) : (@cons _26486 h t) = (term368 _26486 h t).
Proof. exact (TRANS (@lem1126167 _26486 h t) (@lem1126171 _26486 h t)). Qed.
Lemma lem1126174 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f) = (@List.map _26486 _26497 f).
Proof. exact (eq_refl (@List.map _26486 _26497 f)). Qed.
Lemma lem1126175 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term100 _26486 _26497 f h t) = (term369 _26486 _26497 f h t).
Proof. exact (MK_COMB (@lem1126174 _26486 _26497 f) (@lem1126173 _26486 h t)). Qed.
Lemma lem1126177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126178 {_26486 _26497 : Type'} (f : type540 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) f x).
Proof. exact (@lem1126177 (_26486 -> _26497) (type1139 _26486 _26497) f x). Qed.
Lemma lem1126179 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f).
Proof. exact (@lem1126178 _26486 _26497 (@List.map _26486 _26497) f). Qed.
Lemma lem1126180 {_26486 : Type'} (h : _26486) (t : list _26486) : (term368 _26486 h t) = (term368 _26486 h t).
Proof. exact (eq_refl (term368 _26486 h t)). Qed.
Lemma lem1126181 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term369 _26486 _26497 f h t) = (term370 _26486 _26497 f h t).
Proof. exact (MK_COMB (@lem1126179 _26486 _26497 f) (@lem1126180 _26486 h t)). Qed.
Lemma lem1126183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126184 {_26486 _26497 : Type'} (f : type1139 _26486 _26497) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26497) f x).
Proof. exact (@lem1126183 (list _26486) (list _26497) f x). Qed.
Lemma lem1126185 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term370 _26486 _26497 f h t) = (term371 _26486 _26497 f h t).
Proof. exact (@lem1126184 _26486 _26497 (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f) (term368 _26486 h t)). Qed.
Lemma lem1126186 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term369 _26486 _26497 f h t) = (term371 _26486 _26497 f h t).
Proof. exact (TRANS (@lem1126181 _26486 _26497 f h t) (@lem1126185 _26486 _26497 f h t)). Qed.
Lemma lem1126187 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term100 _26486 _26497 f h t) = (term371 _26486 _26497 f h t).
Proof. exact (TRANS (@lem1126175 _26486 _26497 f h t) (@lem1126186 _26486 _26497 f h t)). Qed.
Lemma lem1126194 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126195 {_26486 _26497 : Type'} (f : type540 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) f x).
Proof. exact (@lem1126194 (_26486 -> _26497) (type1139 _26486 _26497) f x). Qed.
Lemma lem1126196 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f).
Proof. exact (@lem1126195 _26486 _26497 (@List.map _26486 _26497) f). Qed.
Lemma lem1126197 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1126198 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (@List.map _26486 _26497 f t') = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t').
Proof. exact (MK_COMB (@lem1126196 _26486 _26497 f) (@lem1126197 _26486 t')). Qed.
Lemma lem1126200 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126201 {_26486 _26497 : Type'} (f : type1139 _26486 _26497) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26497) f x).
Proof. exact (@lem1126200 (list _26486) (list _26497) f x). Qed.
Lemma lem1126202 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t') = (term350 _26486 _26497 f t').
Proof. exact (@lem1126201 _26486 _26497 (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f) t'). Qed.
Lemma lem1126204 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (@List.map _26486 _26497 f t') = (term350 _26486 _26497 f t').
Proof. exact (TRANS (@lem1126198 _26486 _26497 f t') (@lem1126202 _26486 _26497 f t')). Qed.
Lemma lem1126205 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term114 _26486 _26497 f h t) = (term372 _26486 _26497 f h t).
Proof. exact (MK_COMB (@lem1126154 _26497) (@lem1126187 _26486 _26497 f h t)). Qed.
Lemma lem1126206 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : ((term100 _26486 _26497 f h t) = (@List.map _26486 _26497 f t')) = ((term371 _26486 _26497 f h t) = (term350 _26486 _26497 f t')).
Proof. exact (MK_COMB (@lem1126205 _26486 _26497 f h t) (@lem1126204 _26486 _26497 f t')). Qed.
Lemma lem1126207 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1126208 {_26486 : Type'} : (@ALL2 _26486 _26486) = (@ALL2 _26486 _26486).
Proof. exact (eq_refl (@ALL2 _26486 _26486)). Qed.
Lemma lem1126213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126214 {_26486 _26497 : Type'} (f : type545 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) f x).
Proof. exact (@lem1126213 (_26486 -> _26497) (type1402 _26486) f x). Qed.
Lemma lem1126216 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (_18342 f) = (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342 f).
Proof. exact (@lem1126214 _26486 _26497 _18342 f). Qed.
Lemma lem1126223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126224 {_26486 : Type'} (f : type1397 _26486) (x : _26486) : (f x) = (@I (_26486 -> (list _26486) -> list _26486) f x).
Proof. exact (@lem1126223 _26486 (type1138 _26486) f x). Qed.
Lemma lem1126225 {_26486 : Type'} (h : _26486) : (@cons _26486 h) = (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h).
Proof. exact (@lem1126224 _26486 (@cons _26486) h). Qed.
Lemma lem1126226 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126227 {_26486 : Type'} (h : _26486) (t : list _26486) : (@cons _26486 h t) = (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h t).
Proof. exact (MK_COMB (@lem1126225 _26486 h) (@lem1126226 _26486 t)). Qed.
Lemma lem1126229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126230 {_26486 : Type'} (f : type1138 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26486) f x).
Proof. exact (@lem1126229 (list _26486) (list _26486) f x). Qed.
Lemma lem1126231 {_26486 : Type'} (h : _26486) (t : list _26486) : (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h t) = (term368 _26486 h t).
Proof. exact (@lem1126230 _26486 (@I (_26486 -> (list _26486) -> list _26486) (@cons _26486) h) t). Qed.
Lemma lem1126233 {_26486 : Type'} (h : _26486) (t : list _26486) : (@cons _26486 h t) = (term368 _26486 h t).
Proof. exact (TRANS (@lem1126227 _26486 h t) (@lem1126231 _26486 h t)). Qed.
Lemma lem1126234 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1126235 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term190 _26486 _26497 _18342 f) = (term353 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1126208 _26486) (@lem1126216 _26486 _26497 _18342 f)). Qed.
Lemma lem1126236 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term198 _26486 _26497 _18342 f h t) = (term373 _26486 _26497 _18342 f h t).
Proof. exact (MK_COMB (@lem1126235 _26486 _26497 _18342 f) (@lem1126233 _26486 h t)). Qed.
Lemma lem1126237 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) : (term200 _26486 _26497 _18342 f h t t') = (term374 _26486 _26497 _18342 f h t t').
Proof. exact (MK_COMB (@lem1126236 _26486 _26497 _18342 f h t) (@lem1126234 _26486 t')). Qed.
Lemma lem1126239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126240 {_26486 : Type'} (f : type415 _26486) (x : type1402 _26486) : (f x) = (@I ((_26486 -> _26486 -> Prop) -> (list _26486) -> (list _26486) -> Prop) f x).
Proof. exact (@lem1126239 (type1402 _26486) (type1133 _26486) f x). Qed.
Lemma lem1126241 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term353 _26486 _26497 _18342 f) = (term356 _26486 _26497 _18342 f).
Proof. exact (@lem1126240 _26486 (@ALL2 _26486 _26486) (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342 f)). Qed.
Lemma lem1126242 {_26486 : Type'} (h : _26486) (t : list _26486) : (term368 _26486 h t) = (term368 _26486 h t).
Proof. exact (eq_refl (term368 _26486 h t)). Qed.
Lemma lem1126243 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term373 _26486 _26497 _18342 f h t) = (term375 _26486 _26497 _18342 f h t).
Proof. exact (MK_COMB (@lem1126241 _26486 _26497 _18342 f) (@lem1126242 _26486 h t)). Qed.
Lemma lem1126245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126246 {_26486 : Type'} (f : type1133 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> (list _26486) -> Prop) f x).
Proof. exact (@lem1126245 (list _26486) (type1143 _26486) f x). Qed.
Lemma lem1126247 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term375 _26486 _26497 _18342 f h t) = (term376 _26486 _26497 _18342 f h t).
Proof. exact (@lem1126246 _26486 (term356 _26486 _26497 _18342 f) (term368 _26486 h t)). Qed.
Lemma lem1126248 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) : (term373 _26486 _26497 _18342 f h t) = (term376 _26486 _26497 _18342 f h t).
Proof. exact (TRANS (@lem1126243 _26486 _26497 _18342 f h t) (@lem1126247 _26486 _26497 _18342 f h t)). Qed.
Lemma lem1126249 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1126250 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) : (term374 _26486 _26497 _18342 f h t t') = (term377 _26486 _26497 _18342 f h t t').
Proof. exact (MK_COMB (@lem1126248 _26486 _26497 _18342 f h t) (@lem1126249 _26486 t')). Qed.
Lemma lem1126252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126253 {_26486 : Type'} (f : type1143 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> Prop) f x).
Proof. exact (@lem1126252 (list _26486) Prop f x). Qed.
Lemma lem1126254 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) : (term377 _26486 _26497 _18342 f h t t') = (term378 _26486 _26497 _18342 f h t t').
Proof. exact (@lem1126253 _26486 (term376 _26486 _26497 _18342 f h t) t'). Qed.
Lemma lem1126255 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) : (term374 _26486 _26497 _18342 f h t t') = (term378 _26486 _26497 _18342 f h t t').
Proof. exact (TRANS (@lem1126250 _26486 _26497 _18342 f h t t') (@lem1126254 _26486 _26497 _18342 f h t t')). Qed.
Lemma lem1126256 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) : (term200 _26486 _26497 _18342 f h t t') = (term378 _26486 _26497 _18342 f h t t').
Proof. exact (TRANS (@lem1126237 _26486 _26497 _18342 f h t t') (@lem1126255 _26486 _26497 _18342 f h t t')). Qed.
Lemma lem1126257 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) : (term379 _26486 _26497 _18342 f h t t') = (term380 _26486 _26497 _18342 f h t t').
Proof. exact (MK_COMB (@lem1126207) (@lem1126256 _26486 _26497 _18342 f h t t')). Qed.
Lemma lem1126258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1126259 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (h : _26486) (t : list _26486) (t' : list _26486) : (term381 _26486 _26497 _18342 f h t t') = (term382 _26486 _26497 _18342 f h t t').
Proof. exact (MK_COMB (@lem1126258) (@lem1126257 _26486 _26497 _18342 f h t t')). Qed.
Lemma lem1126260 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term348 _26486 _26497 _18342 h t f t') = (term383 _26486 _26497 _18342 h t f t').
Proof. exact (MK_COMB (@lem1126259 _26486 _26497 _18342 f h t t') (@lem1126206 _26486 _26497 h t f t')). Qed.
Lemma lem1126261 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term203 _26486 _26497 _18342 h t f t') : term383 _26486 _26497 _18342 h t f t'.
Proof. exact (EQ_MP (@lem1126260 _26486 _26497 _18342 h t f t') (@lem1125888 _26486 _26497 _18342 h t f t' h1)). Qed.
Lemma lem1126262 {_26486 : Type'} : (@ALL2 _26486 _26486) = (@ALL2 _26486 _26486).
Proof. exact (eq_refl (@ALL2 _26486 _26486)). Qed.
Lemma lem1126267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126268 {_26486 _26497 : Type'} (f : type545 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) f x).
Proof. exact (@lem1126267 (_26486 -> _26497) (type1402 _26486) f x). Qed.
Lemma lem1126270 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (_18342 f) = (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342 f).
Proof. exact (@lem1126268 _26486 _26497 _18342 f). Qed.
Lemma lem1126271 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126272 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1126273 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term190 _26486 _26497 _18342 f) = (term353 _26486 _26497 _18342 f).
Proof. exact (MK_COMB (@lem1126262 _26486) (@lem1126270 _26486 _26497 _18342 f)). Qed.
Lemma lem1126274 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term192 _26486 _26497 _18342 f t) = (term354 _26486 _26497 _18342 f t).
Proof. exact (MK_COMB (@lem1126273 _26486 _26497 _18342 f) (@lem1126271 _26486 t)). Qed.
Lemma lem1126275 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term193 _26486 _26497 _18342 f t t') = (term355 _26486 _26497 _18342 f t t').
Proof. exact (MK_COMB (@lem1126274 _26486 _26497 _18342 f t) (@lem1126272 _26486 t')). Qed.
Lemma lem1126277 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126278 {_26486 : Type'} (f : type415 _26486) (x : type1402 _26486) : (f x) = (@I ((_26486 -> _26486 -> Prop) -> (list _26486) -> (list _26486) -> Prop) f x).
Proof. exact (@lem1126277 (type1402 _26486) (type1133 _26486) f x). Qed.
Lemma lem1126279 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) : (term353 _26486 _26497 _18342 f) = (term356 _26486 _26497 _18342 f).
Proof. exact (@lem1126278 _26486 (@ALL2 _26486 _26486) (@I ((_26486 -> _26497) -> _26486 -> _26486 -> Prop) _18342 f)). Qed.
Lemma lem1126280 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126281 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term354 _26486 _26497 _18342 f t) = (term357 _26486 _26497 _18342 f t).
Proof. exact (MK_COMB (@lem1126279 _26486 _26497 _18342 f) (@lem1126280 _26486 t)). Qed.
Lemma lem1126283 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126284 {_26486 : Type'} (f : type1133 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> (list _26486) -> Prop) f x).
Proof. exact (@lem1126283 (list _26486) (type1143 _26486) f x). Qed.
Lemma lem1126285 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term357 _26486 _26497 _18342 f t) = (term358 _26486 _26497 _18342 f t).
Proof. exact (@lem1126284 _26486 (term356 _26486 _26497 _18342 f) t). Qed.
Lemma lem1126286 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) : (term354 _26486 _26497 _18342 f t) = (term358 _26486 _26497 _18342 f t).
Proof. exact (TRANS (@lem1126281 _26486 _26497 _18342 f t) (@lem1126285 _26486 _26497 _18342 f t)). Qed.
Lemma lem1126287 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1126288 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term355 _26486 _26497 _18342 f t t') = (term359 _26486 _26497 _18342 f t t').
Proof. exact (MK_COMB (@lem1126286 _26486 _26497 _18342 f t) (@lem1126287 _26486 t')). Qed.
Lemma lem1126290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126291 {_26486 : Type'} (f : type1143 _26486) (x : list _26486) : (f x) = (@I ((list _26486) -> Prop) f x).
Proof. exact (@lem1126290 (list _26486) Prop f x). Qed.
Lemma lem1126292 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term359 _26486 _26497 _18342 f t t') = (term360 _26486 _26497 _18342 f t t').
Proof. exact (@lem1126291 _26486 (term358 _26486 _26497 _18342 f t) t'). Qed.
Lemma lem1126293 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term355 _26486 _26497 _18342 f t t') = (term360 _26486 _26497 _18342 f t t').
Proof. exact (TRANS (@lem1126288 _26486 _26497 _18342 f t t') (@lem1126292 _26486 _26497 _18342 f t t')). Qed.
Lemma lem1126294 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term193 _26486 _26497 _18342 f t t') = (term360 _26486 _26497 _18342 f t t').
Proof. exact (TRANS (@lem1126275 _26486 _26497 _18342 f t t') (@lem1126293 _26486 _26497 _18342 f t t')). Qed.
Lemma lem1126295 {_26497 : Type'} : (@eq _26497) = (@eq _26497).
Proof. exact (eq_refl (@eq _26497)). Qed.
Lemma lem1126300 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126301 {_26486 _26497 : Type'} (f : _26486 -> _26497) (x : _26486) : (f x) = (@I (_26486 -> _26497) f x).
Proof. exact (@lem1126300 _26486 _26497 f x). Qed.
Lemma lem1126303 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (f h) = (@I (_26486 -> _26497) f h).
Proof. exact (@lem1126301 _26486 _26497 f h). Qed.
Lemma lem1126308 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126309 {_26486 _26497 : Type'} (f : _26486 -> _26497) (x : _26486) : (f x) = (@I (_26486 -> _26497) f x).
Proof. exact (@lem1126308 _26486 _26497 f x). Qed.
Lemma lem1126311 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h' : _26486) : (f h') = (@I (_26486 -> _26497) f h').
Proof. exact (@lem1126309 _26486 _26497 f h'). Qed.
Lemma lem1126312 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (term384 _26486 _26497 f h) = (term385 _26486 _26497 f h).
Proof. exact (MK_COMB (@lem1126295 _26497) (@lem1126303 _26486 _26497 f h)). Qed.
Lemma lem1126313 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : ((f h) = (f h')) = ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h')).
Proof. exact (MK_COMB (@lem1126312 _26486 _26497 f h) (@lem1126311 _26486 _26497 f h')). Qed.
Lemma lem1126314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1126315 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term147 _26486 _26497 h f h') = (term386 _26486 _26497 h f h').
Proof. exact (MK_COMB (@lem1126314) (@lem1126313 _26486 _26497 h f h')). Qed.
Lemma lem1126316 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term194 _26486 _26497 h h' _18342 f t t') = (term387 _26486 _26497 h h' _18342 f t t').
Proof. exact (MK_COMB (@lem1126315 _26486 _26497 h f h') (@lem1126294 _26486 _26497 _18342 f t t')). Qed.
Lemma lem1126317 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term387 _26486 _26497 h h' _18342 f t t'.
Proof. exact (EQ_MP (@lem1126316 _26486 _26497 h h' _18342 f t t') (@lem1125898 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1126318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1126319 {_26497 : Type'} : (@eq (list _26497)) = (@eq (list _26497)).
Proof. exact (eq_refl (@eq (list _26497))). Qed.
Lemma lem1126326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126327 {_26486 _26497 : Type'} (f : type540 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) f x).
Proof. exact (@lem1126326 (_26486 -> _26497) (type1139 _26486 _26497) f x). Qed.
Lemma lem1126328 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f).
Proof. exact (@lem1126327 _26486 _26497 (@List.map _26486 _26497) f). Qed.
Lemma lem1126329 {_26486 : Type'} (t : list _26486) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1126330 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (@List.map _26486 _26497 f t) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t).
Proof. exact (MK_COMB (@lem1126328 _26486 _26497 f) (@lem1126329 _26486 t)). Qed.
Lemma lem1126332 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126333 {_26486 _26497 : Type'} (f : type1139 _26486 _26497) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26497) f x).
Proof. exact (@lem1126332 (list _26486) (list _26497) f x). Qed.
Lemma lem1126334 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t) = (term350 _26486 _26497 f t).
Proof. exact (@lem1126333 _26486 _26497 (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f) t). Qed.
Lemma lem1126336 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (@List.map _26486 _26497 f t) = (term350 _26486 _26497 f t).
Proof. exact (TRANS (@lem1126330 _26486 _26497 f t) (@lem1126334 _26486 _26497 f t)). Qed.
Lemma lem1126343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126344 {_26486 _26497 : Type'} (f : type540 _26486 _26497) (x : _26486 -> _26497) : (f x) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) f x).
Proof. exact (@lem1126343 (_26486 -> _26497) (type1139 _26486 _26497) f x). Qed.
Lemma lem1126345 {_26486 _26497 : Type'} (f : _26486 -> _26497) : (@List.map _26486 _26497 f) = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f).
Proof. exact (@lem1126344 _26486 _26497 (@List.map _26486 _26497) f). Qed.
Lemma lem1126346 {_26486 : Type'} (t' : list _26486) : t' = t'.
Proof. exact (eq_refl t'). Qed.
Lemma lem1126347 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (@List.map _26486 _26497 f t') = (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t').
Proof. exact (MK_COMB (@lem1126345 _26486 _26497 f) (@lem1126346 _26486 t')). Qed.
Lemma lem1126349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126350 {_26486 _26497 : Type'} (f : type1139 _26486 _26497) (x : list _26486) : (f x) = (@I ((list _26486) -> list _26497) f x).
Proof. exact (@lem1126349 (list _26486) (list _26497) f x). Qed.
Lemma lem1126351 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f t') = (term350 _26486 _26497 f t').
Proof. exact (@lem1126350 _26486 _26497 (@I ((_26486 -> _26497) -> (list _26486) -> list _26497) (@List.map _26486 _26497) f) t'). Qed.
Lemma lem1126353 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (@List.map _26486 _26497 f t') = (term350 _26486 _26497 f t').
Proof. exact (TRANS (@lem1126347 _26486 _26497 f t') (@lem1126351 _26486 _26497 f t')). Qed.
Lemma lem1126354 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t : list _26486) : (term351 _26486 _26497 f t) = (term352 _26486 _26497 f t).
Proof. exact (MK_COMB (@lem1126319 _26497) (@lem1126336 _26486 _26497 f t)). Qed.
Lemma lem1126355 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : ((@List.map _26486 _26497 f t) = (@List.map _26486 _26497 f t')) = ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f t')).
Proof. exact (MK_COMB (@lem1126354 _26486 _26497 f t) (@lem1126353 _26486 _26497 f t')). Qed.
Lemma lem1126356 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term388 _26486 _26497 t f t') = (term389 _26486 _26497 t f t').
Proof. exact (MK_COMB (@lem1126318) (@lem1126355 _26486 _26497 t f t')). Qed.
Lemma lem1126357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1126358 {_26497 : Type'} : (@eq _26497) = (@eq _26497).
Proof. exact (eq_refl (@eq _26497)). Qed.
Lemma lem1126363 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126364 {_26486 _26497 : Type'} (f : _26486 -> _26497) (x : _26486) : (f x) = (@I (_26486 -> _26497) f x).
Proof. exact (@lem1126363 _26486 _26497 f x). Qed.
Lemma lem1126366 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (f h) = (@I (_26486 -> _26497) f h).
Proof. exact (@lem1126364 _26486 _26497 f h). Qed.
Lemma lem1126371 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1126372 {_26486 _26497 : Type'} (f : _26486 -> _26497) (x : _26486) : (f x) = (@I (_26486 -> _26497) f x).
Proof. exact (@lem1126371 _26486 _26497 f x). Qed.
Lemma lem1126374 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h' : _26486) : (f h') = (@I (_26486 -> _26497) f h').
Proof. exact (@lem1126372 _26486 _26497 f h'). Qed.
Lemma lem1126375 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : (term384 _26486 _26497 f h) = (term385 _26486 _26497 f h).
Proof. exact (MK_COMB (@lem1126358 _26497) (@lem1126366 _26486 _26497 f h)). Qed.
Lemma lem1126376 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : ((f h) = (f h')) = ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h')).
Proof. exact (MK_COMB (@lem1126375 _26486 _26497 f h) (@lem1126374 _26486 _26497 f h')). Qed.
Lemma lem1126377 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term390 _26486 _26497 h f h') = (term391 _26486 _26497 h f h').
Proof. exact (MK_COMB (@lem1126357) (@lem1126376 _26486 _26497 h f h')). Qed.
Lemma lem1126378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1126379 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term392 _26486 _26497 h f h') = (term393 _26486 _26497 h f h').
Proof. exact (MK_COMB (@lem1126378) (@lem1126377 _26486 _26497 h f h')). Qed.
Lemma lem1126380 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term349 _26486 _26497 h h' t f t') = (term394 _26486 _26497 h h' t f t').
Proof. exact (MK_COMB (@lem1126379 _26486 _26497 h f h') (@lem1126356 _26486 _26497 t f t')). Qed.
Lemma lem1126381 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term344 _26486 _26497 h h' t f t') : term394 _26486 _26497 h h' t f t'.
Proof. exact (EQ_MP (@lem1126380 _26486 _26497 h h' t f t') (@lem1125910 _26486 _26497 h h' t f t' h1)). Qed.
Lemma lem1126464 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) (h1 : term391 _26486 _26497 h f h') : term391 _26486 _26497 h f h'.
Proof. exact (h1). Qed.
Lemma lem1126541 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) (h1 : term391 _26486 _26497 h f h') : term391 _26486 _26497 h f h'.
Proof. exact (h1). Qed.
Lemma lem1126563 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : (term365 _26486 _26497 _18342 t f m) = (term365 _26486 _26497 _18342 t f m).
Proof. exact (eq_refl (term365 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1126564 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term366 _26486 _26497 _18342 t f) = (term366 _26486 _26497 _18342 t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1126563 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1126565 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1126567 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term367 _26486 _26497 _18342 t f) = (term367 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1126565 _26486) (@lem1126564 _26486 _26497 _18342 t f)). Qed.
Lemma lem1126568 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term367 _26486 _26497 _18342 t f.
Proof. exact (EQ_MP (@lem1126567 _26486 _26497 _18342 t f) (@lem1126153 _26486 _26497 _18342 t f h1)). Qed.
Lemma lem1126618 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term389 _26486 _26497 t f t') : term389 _26486 _26497 t f t'.
Proof. exact (h1). Qed.
Lemma lem1126640 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (m : list _26486) : (term365 _26486 _26497 _18342 t f m) = (term365 _26486 _26497 _18342 t f m).
Proof. exact (eq_refl (term365 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1126641 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term366 _26486 _26497 _18342 t f) = (term366 _26486 _26497 _18342 t f).
Proof. exact (fun_ext (fun m : list _26486 => @lem1126640 _26486 _26497 _18342 t f m)). Qed.
Lemma lem1126642 {_26486 : Type'} : (@all (list _26486)) = (@all (list _26486)).
Proof. exact (eq_refl (@all (list _26486))). Qed.
Lemma lem1126644 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) : (term367 _26486 _26497 _18342 t f) = (term367 _26486 _26497 _18342 t f).
Proof. exact (MK_COMB (@lem1126642 _26486) (@lem1126641 _26486 _26497 _18342 t f)). Qed.
Lemma lem1126645 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term367 _26486 _26497 _18342 t f.
Proof. exact (EQ_MP (@lem1126644 _26486 _26497 _18342 t f) (@lem1126153 _26486 _26497 _18342 t f h1)). Qed.
Lemma lem1126695 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term389 _26486 _26497 t f t') : term389 _26486 _26497 t f t'.
Proof. exact (h1). Qed.
Lemma lem1126760 {_26486 _26497 : Type'} (_18364 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term395 _26486 _26497 _18342 t f _18364.
Proof. exact (@lem1126568 _26486 _26497 _18342 t f h1 _18364). Qed.
Lemma lem1126761 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18364 : list _26486) : (term395 _26486 _26497 _18342 t f _18364) = (term365 _26486 _26497 _18342 t f _18364).
Proof. exact (eq_refl (term395 _26486 _26497 _18342 t f _18364)). Qed.
Lemma lem1126787 {_26486 _26497 : Type'} (_18373 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term395 _26486 _26497 _18342 t f _18373.
Proof. exact (@lem1126645 _26486 _26497 _18342 t f h1 _18373). Qed.
Lemma lem1126788 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18373 : list _26486) : (term395 _26486 _26497 _18342 t f _18373) = (term365 _26486 _26497 _18342 t f _18373).
Proof. exact (eq_refl (term395 _26486 _26497 _18342 t f _18373)). Qed.
Lemma lem1126833 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) (h1 : term391 _26486 _26497 h f h') : term391 _26486 _26497 h f h'.
Proof. exact (h1). Qed.
Lemma lem1126861 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) (h1 : term391 _26486 _26497 h f h') : term391 _26486 _26497 h f h'.
Proof. exact (h1). Qed.
Lemma lem1126871 {_26486 _26497 : Type'} (_18364 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term365 _26486 _26497 _18342 t f _18364.
Proof. exact (EQ_MP (@lem1126761 _26486 _26497 _18342 t f _18364) (@lem1126760 _26486 _26497 _18364 _18342 t f h1)). Qed.
Lemma lem1126889 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term389 _26486 _26497 t f t') : term389 _26486 _26497 t f t'.
Proof. exact (h1). Qed.
Lemma lem1126899 {_26486 _26497 : Type'} (_18373 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term365 _26486 _26497 _18342 t f _18373.
Proof. exact (EQ_MP (@lem1126788 _26486 _26497 _18342 t f _18373) (@lem1126787 _26486 _26497 _18373 _18342 t f h1)). Qed.
Lemma lem1126917 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term389 _26486 _26497 t f t') : term389 _26486 _26497 t f t'.
Proof. exact (h1). Qed.
Lemma lem1127158 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : (@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h').
Proof. exact (proj1 (@lem1126317 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1127159 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term396 _26486 _26497 h f h'.
Proof. exact (fun h0 : term391 _26486 _26497 h f h' => @lem1127158 _26486 _26497 h h' _18342 f t t' h1). Qed.
Lemma lem1127161 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127162 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term396 _26486 _26497 h f h') = ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h')).
Proof. exact (@lem1127161 ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h'))). Qed.
Lemma lem1127163 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : (@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h').
Proof. exact (EQ_MP (@lem1127162 _26486 _26497 h f h') (@lem1127159 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1127166 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1127168 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term391 _26486 _26497 h f h') = (term398 _26486 _26497 h f h').
Proof. exact (@lem1127166 ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h'))). Qed.
Lemma lem1127171 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) (h1 : term391 _26486 _26497 h f h') : term398 _26486 _26497 h f h'.
Proof. exact (EQ_MP (@lem1127168 _26486 _26497 h f h') (@lem1126833 _26486 _26497 h f h' h1)). Qed.
Lemma lem1127174 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (@lem1127171 _26486 _26497 h f h' h1 (@lem1127163 _26486 _26497 h h' _18342 f t t' h2)). Qed.
Lemma lem1127175 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : term399.
Proof. exact (fun h0 : ~ False => @lem1127174 _26486 _26497 h h' _18342 f t t' h1 h2). Qed.
Lemma lem1127177 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127178 : term399 = False.
Proof. exact (@lem1127177 False). Qed.
Lemma lem1127179 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1127178) (@lem1127175 _26486 _26497 h h' _18342 f t t' h1 h2)). Qed.
Lemma lem1127418 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : (@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h').
Proof. exact (proj1 (@lem1126317 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1127419 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term396 _26486 _26497 h f h'.
Proof. exact (fun h0 : term391 _26486 _26497 h f h' => @lem1127418 _26486 _26497 h h' _18342 f t t' h1). Qed.
Lemma lem1127421 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127422 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term396 _26486 _26497 h f h') = ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h')).
Proof. exact (@lem1127421 ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h'))). Qed.
Lemma lem1127423 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : (@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h').
Proof. exact (EQ_MP (@lem1127422 _26486 _26497 h f h') (@lem1127419 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1127426 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1127428 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) : (term391 _26486 _26497 h f h') = (term398 _26486 _26497 h f h').
Proof. exact (@lem1127426 ((@I (_26486 -> _26497) f h) = (@I (_26486 -> _26497) f h'))). Qed.
Lemma lem1127431 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) (h' : _26486) (h1 : term391 _26486 _26497 h f h') : term398 _26486 _26497 h f h'.
Proof. exact (EQ_MP (@lem1127428 _26486 _26497 h f h') (@lem1126861 _26486 _26497 h f h' h1)). Qed.
Lemma lem1127434 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (@lem1127431 _26486 _26497 h f h' h1 (@lem1127423 _26486 _26497 h h' _18342 f t t' h2)). Qed.
Lemma lem1127435 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : term399.
Proof. exact (fun h0 : ~ False => @lem1127434 _26486 _26497 h h' _18342 f t t' h1 h2). Qed.
Lemma lem1127437 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127438 : term399 = False.
Proof. exact (@lem1127437 False). Qed.
Lemma lem1127439 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1127438) (@lem1127435 _26486 _26497 h h' _18342 f t t' h1 h2)). Qed.
Lemma lem1127678 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term360 _26486 _26497 _18342 f t t'.
Proof. exact (proj2 (@lem1126317 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1127679 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term400 _26486 _26497 _18342 f t t'.
Proof. exact (fun h0 : term362 _26486 _26497 _18342 f t t' => @lem1127678 _26486 _26497 h h' _18342 f t t' h1). Qed.
Lemma lem1127681 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127682 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term400 _26486 _26497 _18342 f t t') = (term360 _26486 _26497 _18342 f t t').
Proof. exact (@lem1127681 (term360 _26486 _26497 _18342 f t t')). Qed.
Lemma lem1127683 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term360 _26486 _26497 _18342 f t t'.
Proof. exact (EQ_MP (@lem1127682 _26486 _26497 _18342 f t t') (@lem1127679 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1127689 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1127690 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : (term365 _26486 _26497 _18342 t f _18364) = (term401 _26486 _26497 _18342 f t _18364).
Proof. exact (@lem1127689 ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18364)) (term362 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1127699 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : (term402 _26486 _26497 _18342 t f _18364) = (term403 _26486 _26497 _18342 f t _18364).
Proof. exact (MK_COMB (@lem1127698) (@lem1127690 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127707 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : (term401 _26486 _26497 _18342 f t _18364) = (term401 _26486 _26497 _18342 f t _18364).
Proof. exact (eq_refl (term401 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127708 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : ((term365 _26486 _26497 _18342 t f _18364) = (term401 _26486 _26497 _18342 f t _18364)) = ((term401 _26486 _26497 _18342 f t _18364) = (term401 _26486 _26497 _18342 f t _18364)).
Proof. exact (MK_COMB (@lem1127699 _26486 _26497 _18342 f t _18364) (@lem1127707 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127710 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1127711 (x : Prop) : (x = x) = True.
Proof. exact (@lem1127710 Prop x). Qed.
Lemma lem1127712 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : ((term401 _26486 _26497 _18342 f t _18364) = (term401 _26486 _26497 _18342 f t _18364)) = True.
Proof. exact (@lem1127711 (term401 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127713 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : ((term365 _26486 _26497 _18342 t f _18364) = (term401 _26486 _26497 _18342 f t _18364)) = True.
Proof. exact (TRANS (@lem1127708 _26486 _26497 _18342 f t _18364) (@lem1127712 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127714 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : True = ((term365 _26486 _26497 _18342 t f _18364) = (term401 _26486 _26497 _18342 f t _18364)).
Proof. exact (SYM (@lem1127713 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127715 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : (term365 _26486 _26497 _18342 t f _18364) = (term401 _26486 _26497 _18342 f t _18364).
Proof. exact (EQ_MP (@lem1127714 _26486 _26497 _18342 f t _18364) (@lem0)). Qed.
Lemma lem1127716 {_26486 _26497 : Type'} (_18364 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term401 _26486 _26497 _18342 f t _18364.
Proof. exact (EQ_MP (@lem1127715 _26486 _26497 _18342 f t _18364) (@lem1126871 _26486 _26497 _18364 _18342 t f h1)). Qed.
Lemma lem1127718 (b : Prop) (a : Prop) : (a \/ b) = (term404 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1127719 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18364 : list _26486) : (term401 _26486 _26497 _18342 f t _18364) = (term405 _26486 _26497 _18342 t f _18364).
Proof. exact (@lem1127718 (term362 _26486 _26497 _18342 f t _18364) ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18364))). Qed.
Lemma lem1127721 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1127722 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : (term406 _26486 _26497 _18342 f t _18364) = (term360 _26486 _26497 _18342 f t _18364).
Proof. exact (@lem1127721 (term360 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1127724 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18364 : list _26486) : (term407 _26486 _26497 _18342 f t _18364) = (term408 _26486 _26497 _18342 f t _18364).
Proof. exact (MK_COMB (@lem1127723) (@lem1127722 _26486 _26497 _18342 f t _18364)). Qed.
Lemma lem1127725 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (_18364 : list _26486) : ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18364)) = ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18364)).
Proof. exact (eq_refl ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18364))). Qed.
Lemma lem1127726 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18364 : list _26486) : (term405 _26486 _26497 _18342 t f _18364) = (term409 _26486 _26497 _18342 t f _18364).
Proof. exact (MK_COMB (@lem1127724 _26486 _26497 _18342 f t _18364) (@lem1127725 _26486 _26497 t f _18364)). Qed.
Lemma lem1127727 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18364 : list _26486) : (term401 _26486 _26497 _18342 f t _18364) = (term409 _26486 _26497 _18342 t f _18364).
Proof. exact (TRANS (@lem1127719 _26486 _26497 _18342 t f _18364) (@lem1127726 _26486 _26497 _18342 t f _18364)). Qed.
Lemma lem1127730 {_26486 _26497 : Type'} (_18364 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term409 _26486 _26497 _18342 t f _18364.
Proof. exact (EQ_MP (@lem1127727 _26486 _26497 _18342 t f _18364) (@lem1127716 _26486 _26497 _18364 _18342 t f h1)). Qed.
Lemma lem1127731 {_26486 _26497 : Type'} (_18364 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term409 _26486 _26497 _18342 t f _18364.
Proof. exact (@lem1127730 _26486 _26497 _18364 _18342 t f h1). Qed.
Lemma lem1127732 {_26486 _26497 : Type'} (t' : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term409 _26486 _26497 _18342 t f t'.
Proof. exact (@lem1127731 _26486 _26497 t' _18342 t f h1). Qed.
Lemma lem1127735 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term350 _26486 _26497 f t) = (term350 _26486 _26497 f t').
Proof. exact (@lem1127732 _26486 _26497 t' _18342 t f h1 (@lem1127683 _26486 _26497 h h' _18342 f t t' h2)). Qed.
Lemma lem1127736 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') : term410 _26486 _26497 t f t'.
Proof. exact (fun h0 : term389 _26486 _26497 t f t' => @lem1127735 _26486 _26497 h h' _18342 f t t' h1 h2). Qed.
Lemma lem1127738 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127739 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term410 _26486 _26497 t f t') = ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f t')).
Proof. exact (@lem1127738 ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f t'))). Qed.
Lemma lem1127740 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term350 _26486 _26497 f t) = (term350 _26486 _26497 f t').
Proof. exact (EQ_MP (@lem1127739 _26486 _26497 t f t') (@lem1127736 _26486 _26497 h h' _18342 f t t' h1 h2)). Qed.
Lemma lem1127743 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1127745 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term389 _26486 _26497 t f t') = (term411 _26486 _26497 t f t').
Proof. exact (@lem1127743 ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f t'))). Qed.
Lemma lem1127748 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term389 _26486 _26497 t f t') : term411 _26486 _26497 t f t'.
Proof. exact (EQ_MP (@lem1127745 _26486 _26497 t f t') (@lem1126889 _26486 _26497 t f t' h1)). Qed.
Lemma lem1127751 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (@lem1127748 _26486 _26497 t f t' h2 (@lem1127740 _26486 _26497 h h' _18342 f t t' h1 h3)). Qed.
Lemma lem1127752 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : term399.
Proof. exact (fun h0 : ~ False => @lem1127751 _26486 _26497 h h' _18342 f t t' h1 h2 h3). Qed.
Lemma lem1127754 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127755 : term399 = False.
Proof. exact (@lem1127754 False). Qed.
Lemma lem1127756 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1127755) (@lem1127752 _26486 _26497 h h' _18342 f t t' h1 h2 h3)). Qed.
Lemma lem1127995 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term360 _26486 _26497 _18342 f t t'.
Proof. exact (proj2 (@lem1126317 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1127996 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term400 _26486 _26497 _18342 f t t'.
Proof. exact (fun h0 : term362 _26486 _26497 _18342 f t t' => @lem1127995 _26486 _26497 h h' _18342 f t t' h1). Qed.
Lemma lem1127998 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1127999 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) : (term400 _26486 _26497 _18342 f t t') = (term360 _26486 _26497 _18342 f t t').
Proof. exact (@lem1127998 (term360 _26486 _26497 _18342 f t t')). Qed.
Lemma lem1128000 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term194 _26486 _26497 h h' _18342 f t t') : term360 _26486 _26497 _18342 f t t'.
Proof. exact (EQ_MP (@lem1127999 _26486 _26497 _18342 f t t') (@lem1127996 _26486 _26497 h h' _18342 f t t' h1)). Qed.
Lemma lem1128006 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1128007 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : (term365 _26486 _26497 _18342 t f _18373) = (term401 _26486 _26497 _18342 f t _18373).
Proof. exact (@lem1128006 ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18373)) (term362 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1128016 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : (term402 _26486 _26497 _18342 t f _18373) = (term403 _26486 _26497 _18342 f t _18373).
Proof. exact (MK_COMB (@lem1128015) (@lem1128007 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128024 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : (term401 _26486 _26497 _18342 f t _18373) = (term401 _26486 _26497 _18342 f t _18373).
Proof. exact (eq_refl (term401 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128025 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : ((term365 _26486 _26497 _18342 t f _18373) = (term401 _26486 _26497 _18342 f t _18373)) = ((term401 _26486 _26497 _18342 f t _18373) = (term401 _26486 _26497 _18342 f t _18373)).
Proof. exact (MK_COMB (@lem1128016 _26486 _26497 _18342 f t _18373) (@lem1128024 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128027 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1128028 (x : Prop) : (x = x) = True.
Proof. exact (@lem1128027 Prop x). Qed.
Lemma lem1128029 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : ((term401 _26486 _26497 _18342 f t _18373) = (term401 _26486 _26497 _18342 f t _18373)) = True.
Proof. exact (@lem1128028 (term401 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128030 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : ((term365 _26486 _26497 _18342 t f _18373) = (term401 _26486 _26497 _18342 f t _18373)) = True.
Proof. exact (TRANS (@lem1128025 _26486 _26497 _18342 f t _18373) (@lem1128029 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128031 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : True = ((term365 _26486 _26497 _18342 t f _18373) = (term401 _26486 _26497 _18342 f t _18373)).
Proof. exact (SYM (@lem1128030 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128032 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : (term365 _26486 _26497 _18342 t f _18373) = (term401 _26486 _26497 _18342 f t _18373).
Proof. exact (EQ_MP (@lem1128031 _26486 _26497 _18342 f t _18373) (@lem0)). Qed.
Lemma lem1128033 {_26486 _26497 : Type'} (_18373 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term401 _26486 _26497 _18342 f t _18373.
Proof. exact (EQ_MP (@lem1128032 _26486 _26497 _18342 f t _18373) (@lem1126899 _26486 _26497 _18373 _18342 t f h1)). Qed.
Lemma lem1128035 (b : Prop) (a : Prop) : (a \/ b) = (term404 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1128036 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18373 : list _26486) : (term401 _26486 _26497 _18342 f t _18373) = (term405 _26486 _26497 _18342 t f _18373).
Proof. exact (@lem1128035 (term362 _26486 _26497 _18342 f t _18373) ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18373))). Qed.
Lemma lem1128038 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1128039 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : (term406 _26486 _26497 _18342 f t _18373) = (term360 _26486 _26497 _18342 f t _18373).
Proof. exact (@lem1128038 (term360 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128041 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (_18373 : list _26486) : (term407 _26486 _26497 _18342 f t _18373) = (term408 _26486 _26497 _18342 f t _18373).
Proof. exact (MK_COMB (@lem1128040) (@lem1128039 _26486 _26497 _18342 f t _18373)). Qed.
Lemma lem1128042 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (_18373 : list _26486) : ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18373)) = ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18373)).
Proof. exact (eq_refl ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f _18373))). Qed.
Lemma lem1128043 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18373 : list _26486) : (term405 _26486 _26497 _18342 t f _18373) = (term409 _26486 _26497 _18342 t f _18373).
Proof. exact (MK_COMB (@lem1128041 _26486 _26497 _18342 f t _18373) (@lem1128042 _26486 _26497 t f _18373)). Qed.
Lemma lem1128044 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (_18373 : list _26486) : (term401 _26486 _26497 _18342 f t _18373) = (term409 _26486 _26497 _18342 t f _18373).
Proof. exact (TRANS (@lem1128036 _26486 _26497 _18342 t f _18373) (@lem1128043 _26486 _26497 _18342 t f _18373)). Qed.
Lemma lem1128047 {_26486 _26497 : Type'} (_18373 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term409 _26486 _26497 _18342 t f _18373.
Proof. exact (EQ_MP (@lem1128044 _26486 _26497 _18342 t f _18373) (@lem1128033 _26486 _26497 _18373 _18342 t f h1)). Qed.
Lemma lem1128048 {_26486 _26497 : Type'} (_18373 : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term409 _26486 _26497 _18342 t f _18373.
Proof. exact (@lem1128047 _26486 _26497 _18373 _18342 t f h1). Qed.
Lemma lem1128049 {_26486 _26497 : Type'} (t' : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term409 _26486 _26497 _18342 t f t'.
Proof. exact (@lem1128048 _26486 _26497 t' _18342 t f h1). Qed.
Lemma lem1128052 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term350 _26486 _26497 f t) = (term350 _26486 _26497 f t').
Proof. exact (@lem1128049 _26486 _26497 t' _18342 t f h1 (@lem1128000 _26486 _26497 h h' _18342 f t t' h2)). Qed.
Lemma lem1128053 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') : term410 _26486 _26497 t f t'.
Proof. exact (fun h0 : term389 _26486 _26497 t f t' => @lem1128052 _26486 _26497 h h' _18342 f t t' h1 h2). Qed.
Lemma lem1128055 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1128056 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term410 _26486 _26497 t f t') = ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f t')).
Proof. exact (@lem1128055 ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f t'))). Qed.
Lemma lem1128057 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term350 _26486 _26497 f t) = (term350 _26486 _26497 f t').
Proof. exact (EQ_MP (@lem1128056 _26486 _26497 t f t') (@lem1128053 _26486 _26497 h h' _18342 f t t' h1 h2)). Qed.
Lemma lem1128060 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1128062 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term389 _26486 _26497 t f t') = (term411 _26486 _26497 t f t').
Proof. exact (@lem1128060 ((term350 _26486 _26497 f t) = (term350 _26486 _26497 f t'))). Qed.
Lemma lem1128065 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term389 _26486 _26497 t f t') : term411 _26486 _26497 t f t'.
Proof. exact (EQ_MP (@lem1128062 _26486 _26497 t f t') (@lem1126917 _26486 _26497 t f t' h1)). Qed.
Lemma lem1128068 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (@lem1128065 _26486 _26497 t f t' h2 (@lem1128057 _26486 _26497 h h' _18342 f t t' h1 h3)). Qed.
Lemma lem1128069 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : term399.
Proof. exact (fun h0 : ~ False => @lem1128068 _26486 _26497 h h' _18342 f t t' h1 h2 h3). Qed.
Lemma lem1128071 (p : Prop) : (term397 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1128072 : term399 = False.
Proof. exact (@lem1128071 False). Qed.
Lemma lem1128073 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128072) (@lem1128069 _26486 _26497 h h' _18342 f t t' h1 h2 h3)). Qed.
Lemma lem1128074 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : (term389 _26486 _26497 t f t') = False.
Proof. exact (prop_ext (fun h4 : term389 _26486 _26497 t f t' => @lem1128073 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (fun h4 : False => @lem1126917 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128075 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128074 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (@lem1126917 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128076 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : (term389 _26486 _26497 t f t') = False.
Proof. exact (prop_ext (fun h4 : term389 _26486 _26497 t f t' => @lem1127756 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (fun h4 : False => @lem1126889 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128077 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128076 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (@lem1126889 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128078 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term391 _26486 _26497 h f h') = False.
Proof. exact (prop_ext (fun h3 : term391 _26486 _26497 h f h' => @lem1127439 _26486 _26497 h h' _18342 f t t' h1 h2) (fun h3 : False => @lem1126861 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128079 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128078 _26486 _26497 h h' _18342 f t t' h1 h2) (@lem1126861 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128080 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term391 _26486 _26497 h f h') = False.
Proof. exact (prop_ext (fun h3 : term391 _26486 _26497 h f h' => @lem1127179 _26486 _26497 h h' _18342 f t t' h1 h2) (fun h3 : False => @lem1126833 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128081 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128080 _26486 _26497 h h' _18342 f t t' h1 h2) (@lem1126833 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128082 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : (term389 _26486 _26497 t f t') = False.
Proof. exact (prop_ext (fun h4 : term389 _26486 _26497 t f t' => @lem1128075 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (fun h4 : False => @lem1126695 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128083 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128082 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (@lem1126695 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128084 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : (term389 _26486 _26497 t f t') = False.
Proof. exact (prop_ext (fun h4 : term389 _26486 _26497 t f t' => @lem1128077 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (fun h4 : False => @lem1126618 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128085 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128084 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (@lem1126618 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128086 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term391 _26486 _26497 h f h') = False.
Proof. exact (prop_ext (fun h3 : term391 _26486 _26497 h f h' => @lem1128079 _26486 _26497 h h' _18342 f t t' h1 h2) (fun h3 : False => @lem1126541 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128087 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128086 _26486 _26497 h h' _18342 f t t' h1 h2) (@lem1126541 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128088 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term391 _26486 _26497 h f h') = False.
Proof. exact (prop_ext (fun h3 : term391 _26486 _26497 h f h' => @lem1128081 _26486 _26497 h h' _18342 f t t' h1 h2) (fun h3 : False => @lem1126464 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128089 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128088 _26486 _26497 h h' _18342 f t t' h1 h2) (@lem1126464 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128090 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : (term389 _26486 _26497 t f t') = False.
Proof. exact (prop_ext (fun h4 : term389 _26486 _26497 t f t' => @lem1128083 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (fun h4 : False => @lem1126695 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128091 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128090 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (@lem1126695 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128092 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : (term389 _26486 _26497 t f t') = False.
Proof. exact (prop_ext (fun h4 : term389 _26486 _26497 t f t' => @lem1128085 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (fun h4 : False => @lem1126618 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128093 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128092 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (@lem1126618 _26486 _26497 t f t' h2)). Qed.
Lemma lem1128094 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term391 _26486 _26497 h f h') = False.
Proof. exact (prop_ext (fun h3 : term391 _26486 _26497 h f h' => @lem1128087 _26486 _26497 h h' _18342 f t t' h1 h2) (fun h3 : False => @lem1126541 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128095 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128094 _26486 _26497 h h' _18342 f t t' h1 h2) (@lem1126541 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128096 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : (term391 _26486 _26497 h f h') = False.
Proof. exact (prop_ext (fun h3 : term391 _26486 _26497 h f h' => @lem1128089 _26486 _26497 h h' _18342 f t t' h1 h2) (fun h3 : False => @lem1126464 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128097 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t : list _26486) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') : False.
Proof. exact (EQ_MP (@lem1128096 _26486 _26497 h h' _18342 f t t' h1 h2) (@lem1126464 _26486 _26497 h f h' h1)). Qed.
Lemma lem1128098 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term389 _26486 _26497 t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') (h4 : term203 _26486 _26497 _18342 h t f t') : False.
Proof. exact (or_elim (@lem1126261 _26486 _26497 _18342 h t f t' h4) (fun h0 : term380 _26486 _26497 _18342 f h t t' => @lem1128093 _26486 _26497 h h' _18342 f t t' h1 h2 h3) (fun h0 : (term371 _26486 _26497 f h t) = (term350 _26486 _26497 f t') => @lem1128091 _26486 _26497 h h' _18342 f t t' h1 h2 h3)). Qed.
Lemma lem1128099 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term391 _26486 _26497 h f h') (h2 : term194 _26486 _26497 h h' _18342 f t t') (h3 : term203 _26486 _26497 _18342 h t f t') : False.
Proof. exact (or_elim (@lem1126261 _26486 _26497 _18342 h t f t' h3) (fun h0 : term380 _26486 _26497 _18342 f h t t' => @lem1128097 _26486 _26497 h h' _18342 f t t' h1 h2) (fun h0 : (term371 _26486 _26497 f h t) = (term350 _26486 _26497 f t') => @lem1128095 _26486 _26497 h h' _18342 f t t' h1 h2)). Qed.
Lemma lem1128100 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term344 _26486 _26497 h h' t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') (h4 : term203 _26486 _26497 _18342 h t f t') : False.
Proof. exact (or_elim (@lem1126381 _26486 _26497 h h' t f t' h2) (fun h0 : term391 _26486 _26497 h f h' => @lem1128099 _26486 _26497 h' _18342 h t f t' h0 h3 h4) (fun h0 : term389 _26486 _26497 t f t' => @lem1128098 _26486 _26497 h' _18342 h t f t' h1 h0 h3 h4)). Qed.
Lemma lem1128101 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term344 _26486 _26497 h h' t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') (h4 : term203 _26486 _26497 _18342 h t f t') : (term194 _26486 _26497 h h' _18342 f t t') = False.
Proof. exact (prop_ext (fun h5 : term194 _26486 _26497 h h' _18342 f t t' => @lem1128100 _26486 _26497 h' _18342 h t f t' h1 h2 h3 h4) (fun h5 : False => @lem1125898 _26486 _26497 h h' _18342 f t t' h3)). Qed.
Lemma lem1128102 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term344 _26486 _26497 h h' t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') (h4 : term203 _26486 _26497 _18342 h t f t') : False.
Proof. exact (EQ_MP (@lem1128101 _26486 _26497 h' _18342 h t f t' h1 h2 h3 h4) (@lem1125898 _26486 _26497 h h' _18342 f t t' h3)). Qed.
Lemma lem1128103 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term344 _26486 _26497 h h' t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') (h4 : term203 _26486 _26497 _18342 h t f t') : (term344 _26486 _26497 h h' t f t') = False.
Proof. exact (prop_ext (fun h5 : term344 _26486 _26497 h h' t f t' => @lem1128102 _26486 _26497 h' _18342 h t f t' h1 h2 h3 h4) (fun h5 : False => @lem1125356 _26486 _26497 h h' t f t' h2)). Qed.
Lemma lem1128104 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term344 _26486 _26497 h h' t f t') (h3 : term194 _26486 _26497 h h' _18342 f t t') (h4 : term203 _26486 _26497 _18342 h t f t') : False.
Proof. exact (EQ_MP (@lem1128103 _26486 _26497 h' _18342 h t f t' h1 h2 h3 h4) (@lem1125356 _26486 _26497 h h' t f t' h2)). Qed.
Lemma lem1128105 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') (h3 : term203 _26486 _26497 _18342 h t f t') : term343 _26486 _26497 h h' t f t'.
Proof. exact (fun h0 : term344 _26486 _26497 h h' t f t' => @lem1128104 _26486 _26497 h' _18342 h t f t' h1 h0 h2 h3). Qed.
Lemma lem1128106 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term194 _26486 _26497 h h' _18342 f t t') (h3 : term203 _26486 _26497 _18342 h t f t') : term152 _26486 _26497 h h' t f t'.
Proof. exact (EQ_MP (@lem1125355 _26486 _26497 h h' t f t') (@lem1128105 _26486 _26497 h' _18342 h t f t' h1 h2 h3)). Qed.
Lemma lem1128107 {_26486 _26497 : Type'} (h' : _26486) (_18342 : type545 _26486 _26497) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term212 _26486 _26497 _18342 t f) (h2 : term203 _26486 _26497 _18342 h t f t') : term196 _26486 _26497 _18342 h h' t f t'.
Proof. exact (fun h0 : term194 _26486 _26497 h h' _18342 f t t' => @lem1128106 _26486 _26497 h' _18342 h t f t' h1 h0 h2). Qed.
Lemma lem1128108 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t' : list _26486) (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (h1 : term212 _26486 _26497 _18342 t f) : term205 _26486 _26497 _18342 h h' t f t'.
Proof. exact (fun h0 : term203 _26486 _26497 _18342 h t f t' => @lem1128107 _26486 _26497 h' _18342 h t f t' h1 h0). Qed.
Lemma lem1128109 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term214 _26486 _26497 _18342 h h' t f t'.
Proof. exact (fun h0 : term212 _26486 _26497 _18342 t f => @lem1128108 _26486 _26497 h h' t' _18342 t f h0). Qed.
Lemma lem1128114 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term216 _26486 _26497 _18342 h' t f t'.
Proof. exact (fun h : _26486 => @lem1128109 _26486 _26497 _18342 h h' t f t'). Qed.
Lemma lem1128119 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term218 _26486 _26497 _18342 t f t'.
Proof. exact (fun h' : _26486 => @lem1128114 _26486 _26497 _18342 h' t f t'). Qed.
Lemma lem1128124 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (f : _26486 -> _26497) (t' : list _26486) : term220 _26486 _26497 _18342 f t'.
Proof. exact (fun t : list _26486 => @lem1128119 _26486 _26497 _18342 t f t'). Qed.
Lemma lem1128129 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) (t' : list _26486) : term222 _26486 _26497 _18342 t'.
Proof. exact (fun f : _26486 -> _26497 => @lem1128124 _26486 _26497 _18342 f t'). Qed.
Lemma lem1128134 {_26486 _26497 : Type'} (_18342 : type545 _26486 _26497) : term224 _26486 _26497 _18342.
Proof. exact (fun t' : list _26486 => @lem1128129 _26486 _26497 _18342 t'). Qed.
Lemma lem1128135 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) (_18342 : type545 _26486 _26497) : term284 _26486 _26497 _18343 _18342.
Proof. exact (fun h0 : term282 _26486 _26497 _18342 _18343 => @lem1128134 _26486 _26497 _18342). Qed.
Lemma lem1128140 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : term286 _26486 _26497 _18343.
Proof. exact (fun _18342 : type545 _26486 _26497 => @lem1128135 _26486 _26497 _18343 _18342). Qed.
Lemma lem1128141 {_26486 _26497 : Type'} (_18343 : type1360 _26486 _26497) : term340 _26486 _26497 _18343.
Proof. exact (fun h0 : term338 _26486 _26497 _18343 => @lem1128140 _26486 _26497 _18343). Qed.
Lemma lem1128146 {_26486 _26497 : Type'} : term342 _26486 _26497.
Proof. exact (fun _18343 : type1360 _26486 _26497 => @lem1128141 _26486 _26497 _18343). Qed.
Lemma lem1128147 {_26486 _26497 : Type'} : term184 _26486 _26497.
Proof. exact (EQ_MP (@lem1125346 _26486 _26497) (@lem1128146 _26486 _26497)). Qed.
Lemma lem1128148 {_26486 _26497 : Type'} (t' : list _26486) : term412 _26486 _26497 t'.
Proof. exact (@lem1128147 _26486 _26497 t'). Qed.
Lemma lem1128149 {_26486 _26497 : Type'} (t' : list _26486) : (term412 _26486 _26497 t') = (term180 _26486 _26497 t').
Proof. exact (eq_refl (term412 _26486 _26497 t')). Qed.
Lemma lem1128150 {_26486 _26497 : Type'} (t' : list _26486) : term180 _26486 _26497 t'.
Proof. exact (EQ_MP (@lem1128149 _26486 _26497 t') (@lem1128148 _26486 _26497 t')). Qed.
Lemma lem1128151 {_26486 _26497 : Type'} (t' : list _26486) (f : _26486 -> _26497) : term413 _26486 _26497 t' f.
Proof. exact (@lem1128150 _26486 _26497 t' f). Qed.
Lemma lem1128152 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : (term413 _26486 _26497 t' f) = (term176 _26486 _26497 f t').
Proof. exact (eq_refl (term413 _26486 _26497 t' f)). Qed.
Lemma lem1128153 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) : term176 _26486 _26497 f t'.
Proof. exact (EQ_MP (@lem1128152 _26486 _26497 f t') (@lem1128151 _26486 _26497 t' f)). Qed.
Lemma lem1128154 {_26486 _26497 : Type'} (f : _26486 -> _26497) (t' : list _26486) (t : list _26486) : term414 _26486 _26497 f t' t.
Proof. exact (@lem1128153 _26486 _26497 f t' t). Qed.
Lemma lem1128155 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term414 _26486 _26497 f t' t) = (term172 _26486 _26497 t f t').
Proof. exact (eq_refl (term414 _26486 _26497 f t' t)). Qed.
Lemma lem1128156 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term172 _26486 _26497 t f t'.
Proof. exact (EQ_MP (@lem1128155 _26486 _26497 t f t') (@lem1128154 _26486 _26497 f t' t)). Qed.
Lemma lem1128157 {_26486 _26497 : Type'} (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h' : _26486) : term415 _26486 _26497 t f t' h'.
Proof. exact (@lem1128156 _26486 _26497 t f t' h'). Qed.
Lemma lem1128158 {_26486 _26497 : Type'} (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term415 _26486 _26497 t f t' h') = (term168 _26486 _26497 h' t f t').
Proof. exact (eq_refl (term415 _26486 _26497 t f t' h')). Qed.
Lemma lem1128159 {_26486 _26497 : Type'} (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term168 _26486 _26497 h' t f t'.
Proof. exact (EQ_MP (@lem1128158 _26486 _26497 h' t f t') (@lem1128157 _26486 _26497 t f t' h')). Qed.
Lemma lem1128160 {_26486 _26497 : Type'} (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h : _26486) : term416 _26486 _26497 h' t f t' h.
Proof. exact (@lem1128159 _26486 _26497 h' t f t' h). Qed.
Lemma lem1128161 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : (term416 _26486 _26497 h' t f t' h) = (term157 _26486 _26497 h h' t f t').
Proof. exact (eq_refl (term416 _26486 _26497 h' t f t' h)). Qed.
Lemma lem1128162 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term157 _26486 _26497 h h' t f t'.
Proof. exact (EQ_MP (@lem1128161 _26486 _26497 h h' t f t') (@lem1128160 _26486 _26497 h' t f t' h)). Qed.
Lemma lem1128164 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) : term157 _26486 _26497 h h' t f t'.
Proof. exact (@lem1124579 _26486 _26497 h h' t f t' (@lem1128162 _26486 _26497 h h' t f t')). Qed.
Lemma lem1128165 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t' : list _26486) (t : list _26486) (f : _26486 -> _26497) (h1 : term8 _26486 _26497 t f) : term163 _26486 _26497 h h' t f t'.
Proof. exact (@lem1128164 _26486 _26497 h h' t f t' (@lem1124198 _26486 _26497 t f h1)). Qed.
Lemma lem1128166 {_26486 _26497 : Type'} (h' : _26486) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term8 _26486 _26497 t f) (h2 : term67 _26486 _26497 h t f t') : term155 _26486 _26497 h h' t f t'.
Proof. exact (@lem1128165 _26486 _26497 h h' t' t f h1 (@lem1124258 _26486 _26497 h t f t' h2)). Qed.
Lemma lem1128167 {_26486 _26497 : Type'} (h' : _26486) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term8 _26486 _26497 t f) (h2 : term156 _26486 _26497 h h' t f t') (h3 : term67 _26486 _26497 h t f t') : False.
Proof. exact (@lem1128166 _26486 _26497 h' h t f t' h1 h3 (@lem1124563 _26486 _26497 h h' t f t' h2)). Qed.
Lemma lem1128168 {_26486 _26497 : Type'} (h' : _26486) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term8 _26486 _26497 t f) (h2 : term156 _26486 _26497 h h' t f t') (h3 : term67 _26486 _26497 h t f t') : (term156 _26486 _26497 h h' t f t') = False.
Proof. exact (prop_ext (fun h4 : term156 _26486 _26497 h h' t f t' => @lem1128167 _26486 _26497 h' h t f t' h1 h2 h3) (fun h4 : False => @lem1124563 _26486 _26497 h h' t f t' h2)). Qed.
Lemma lem1128169 {_26486 _26497 : Type'} (h' : _26486) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term8 _26486 _26497 t f) (h2 : term156 _26486 _26497 h h' t f t') (h3 : term67 _26486 _26497 h t f t') : False.
Proof. exact (EQ_MP (@lem1128168 _26486 _26497 h' h t f t' h1 h2 h3) (@lem1124563 _26486 _26497 h h' t f t' h2)). Qed.
Lemma lem1128170 {_26486 _26497 : Type'} (h' : _26486) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term8 _26486 _26497 t f) (h2 : term67 _26486 _26497 h t f t') : term155 _26486 _26497 h h' t f t'.
Proof. exact (fun h0 : term156 _26486 _26497 h h' t f t' => @lem1128169 _26486 _26497 h' h t f t' h1 h0 h2). Qed.
Lemma lem1128171 {_26486 _26497 : Type'} (h' : _26486) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term8 _26486 _26497 t f) (h2 : term67 _26486 _26497 h t f t') : term153 _26486 _26497 h h' t f t'.
Proof. exact (EQ_MP (@lem1124562 _26486 _26497 h h' t f t') (@lem1128170 _26486 _26497 h' h t f t' h1 h2)). Qed.
Lemma lem1128172 {_26486 _26497 : Type'} (h' : _26486) (h : _26486) (t : list _26486) (f : _26486 -> _26497) (t' : list _26486) (h1 : term8 _26486 _26497 t f) (h2 : term67 _26486 _26497 h t f t') : term71 _26486 _26497 h t f h' t'.
Proof. exact (EQ_MP (@lem1124558 _26486 _26497 h t f h' t') (@lem1128171 _26486 _26497 h' h t f t' h1 h2)). Qed.
Lemma lem1128173 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t' : list _26486) (t : list _26486) (f : _26486 -> _26497) (h1 : term8 _26486 _26497 t f) : term73 _26486 _26497 h t f h' t'.
Proof. exact (fun h0 : term67 _26486 _26497 h t f t' => @lem1128172 _26486 _26497 h' h t f t' h1 h0). Qed.
Lemma lem1128178 {_26486 _26497 : Type'} (h : _26486) (h' : _26486) (t : list _26486) (f : _26486 -> _26497) (h1 : term8 _26486 _26497 t f) : term77 _26486 _26497 h t f h'.
Proof. exact (fun t' : list _26486 => @lem1128173 _26486 _26497 h h' t' t f h1). Qed.
Lemma lem1128183 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h1 : term8 _26486 _26497 t f) : term81 _26486 _26497 h t f.
Proof. exact (fun h' : _26486 => @lem1128178 _26486 _26497 h h' t f h1). Qed.
Lemma lem1128184 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h1 : term8 _26486 _26497 t f) : term83 _26486 _26497 h t f.
Proof. exact (conj (@lem1124440 _26486 _26497 h t f) (@lem1128183 _26486 _26497 h t f h1)). Qed.
Lemma lem1128185 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) (h1 : term8 _26486 _26497 t f) : term12 _26486 _26497 h t f.
Proof. exact (@lem1124257 _26486 _26497 h t f (@lem1128184 _26486 _26497 h t f h1)). Qed.
Lemma lem1128186 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) (t : list _26486) : term44 _26486 _26497 f h t.
Proof. exact (fun h0 : term38 _26486 _26497 f t => @lem1124375 _26486 _26497 f h t). Qed.
Lemma lem1128191 {_26486 _26497 : Type'} (f : _26486 -> _26497) (h : _26486) : term48 _26486 _26497 f h.
Proof. exact (fun t : list _26486 => @lem1128186 _26486 _26497 f h t). Qed.
Lemma lem1128196 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term52 _26486 _26497 f.
Proof. exact (fun h : _26486 => @lem1128191 _26486 _26497 f h). Qed.
Lemma lem1128197 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term54 _26486 _26497 f.
Proof. exact (conj (@lem1124313 _26486 _26497 f) (@lem1128196 _26486 _26497 f)). Qed.
Lemma lem1128198 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term4 _26486 _26497 f.
Proof. exact (@lem1124225 _26486 _26497 f (@lem1128197 _26486 _26497 f)). Qed.
Lemma lem1128199 {_26486 _26497 : Type'} (h : _26486) (t : list _26486) (f : _26486 -> _26497) : term14 _26486 _26497 h t f.
Proof. exact (fun h0 : term8 _26486 _26497 t f => @lem1128185 _26486 _26497 h t f h0). Qed.
Lemma lem1128204 {_26486 _26497 : Type'} (h : _26486) (f : _26486 -> _26497) : term18 _26486 _26497 h f.
Proof. exact (fun t : list _26486 => @lem1128199 _26486 _26497 h t f). Qed.
Lemma lem1128209 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term22 _26486 _26497 f.
Proof. exact (fun h : _26486 => @lem1128204 _26486 _26497 h f). Qed.
Lemma lem1128210 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term24 _26486 _26497 f.
Proof. exact (conj (@lem1128198 _26486 _26497 f) (@lem1128209 _26486 _26497 f)). Qed.
Lemma lem1128211 {_26486 _26497 : Type'} (f : _26486 -> _26497) : term29 _26486 _26497 f.
Proof. exact (@lem1124197 _26486 _26497 f (@lem1128210 _26486 _26497 f)). Qed.
