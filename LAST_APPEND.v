Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAST_APPEND_term_abbrevs.
Require Import APPEND_EQ_NIL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1098347_spec.
Require Import thm1098348_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21750_spec.
Lemma lem1202171 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1202172 {_28101 : Type'} (P : type1143 _28101) : term0 _28101 P.
Proof. exact (@lem1202171 _28101 P). Qed.
Lemma lem1202173 {_28101 : Type'} : term1 _28101.
Proof. exact (@lem1202172 _28101 (term2 _28101)). Qed.
Lemma lem1202174 {_28101 : Type'} : (term3 _28101) = (term4 _28101).
Proof. exact (eq_refl (term3 _28101)). Qed.
Lemma lem1202175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1202176 {_28101 : Type'} : (term5 _28101) = (term6 _28101).
Proof. exact (MK_COMB (@lem1202175) (@lem1202174 _28101)). Qed.
Lemma lem1202177 {_28101 : Type'} (t : list _28101) : (term7 _28101 t) = (term8 _28101 t).
Proof. exact (eq_refl (term7 _28101 t)). Qed.
Lemma lem1202178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1202179 {_28101 : Type'} (t : list _28101) : (term9 _28101 t) = (term10 _28101 t).
Proof. exact (MK_COMB (@lem1202178) (@lem1202177 _28101 t)). Qed.
Lemma lem1202180 {_28101 : Type'} (h : _28101) (t : list _28101) : (term11 _28101 h t) = (term12 _28101 h t).
Proof. exact (eq_refl (term11 _28101 h t)). Qed.
Lemma lem1202181 {_28101 : Type'} (h : _28101) (t : list _28101) : (term13 _28101 h t) = (term14 _28101 h t).
Proof. exact (MK_COMB (@lem1202179 _28101 t) (@lem1202180 _28101 h t)). Qed.
Lemma lem1202182 {_28101 : Type'} (h : _28101) : (term15 _28101 h) = (term16 _28101 h).
Proof. exact (fun_ext (fun t : list _28101 => @lem1202181 _28101 h t)). Qed.
Lemma lem1202183 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202184 {_28101 : Type'} (h : _28101) : (term17 _28101 h) = (term18 _28101 h).
Proof. exact (MK_COMB (@lem1202183 _28101) (@lem1202182 _28101 h)). Qed.
Lemma lem1202185 {_28101 : Type'} : (term19 _28101) = (term20 _28101).
Proof. exact (fun_ext (fun h : _28101 => @lem1202184 _28101 h)). Qed.
Lemma lem1202186 {_28101 : Type'} : (@all _28101) = (@all _28101).
Proof. exact (eq_refl (@all _28101)). Qed.
Lemma lem1202187 {_28101 : Type'} : (term21 _28101) = (term22 _28101).
Proof. exact (MK_COMB (@lem1202186 _28101) (@lem1202185 _28101)). Qed.
Lemma lem1202188 {_28101 : Type'} : (term23 _28101) = (term24 _28101).
Proof. exact (MK_COMB (@lem1202176 _28101) (@lem1202187 _28101)). Qed.
Lemma lem1202189 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1202190 {_28101 : Type'} : (term25 _28101) = (term26 _28101).
Proof. exact (MK_COMB (@lem1202189) (@lem1202188 _28101)). Qed.
Lemma lem1202191 {_28101 : Type'} (p : list _28101) : (term7 _28101 p) = (term8 _28101 p).
Proof. exact (eq_refl (term7 _28101 p)). Qed.
Lemma lem1202192 {_28101 : Type'} : (term27 _28101) = (term2 _28101).
Proof. exact (fun_ext (fun p : list _28101 => @lem1202191 _28101 p)). Qed.
Lemma lem1202193 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202194 {_28101 : Type'} : (term28 _28101) = (term29 _28101).
Proof. exact (MK_COMB (@lem1202193 _28101) (@lem1202192 _28101)). Qed.
Lemma lem1202195 {_28101 : Type'} : (term1 _28101) = (term30 _28101).
Proof. exact (MK_COMB (@lem1202190 _28101) (@lem1202194 _28101)). Qed.
Lemma lem1202196 {_28101 : Type'} : term30 _28101.
Proof. exact (EQ_MP (@lem1202195 _28101) (@lem1202173 _28101)). Qed.
Lemma lem1202197 {_28101 : Type'} (t : list _28101) (h1 : term8 _28101 t) : term8 _28101 t.
Proof. exact (h1). Qed.
Lemma lem1202214 {A : Type'} : term31 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1202215 {A : Type'} (l : list A) : term32 A l.
Proof. exact (@lem1202214 A l). Qed.
Lemma lem1202216 {A : Type'} (l : list A) : (term32 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term32 A l)). Qed.
Lemma lem1202225 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1202216 A l) (@lem1202215 A l)). Qed.
Lemma lem1202226 {_28101 : Type'} (l : list _28101) : (@List.app _28101 (@nil _28101) l) = l.
Proof. exact (@lem1202225 _28101 l). Qed.
Lemma lem1202227 {_28101 : Type'} (q : list _28101) : (@List.app _28101 (@nil _28101) q) = q.
Proof. exact (@lem1202226 _28101 q). Qed.
Lemma lem1202228 {_28101 : Type'} : (@LAST _28101) = (@LAST _28101).
Proof. exact (eq_refl (@LAST _28101)). Qed.
Lemma lem1202229 {_28101 : Type'} (q : list _28101) : (term33 _28101 q) = (@LAST _28101 q).
Proof. exact (MK_COMB (@lem1202228 _28101) (@lem1202227 _28101 q)). Qed.
Lemma lem1202230 {_28101 : Type'} : (@eq _28101) = (@eq _28101).
Proof. exact (eq_refl (@eq _28101)). Qed.
Lemma lem1202231 {_28101 : Type'} (q : list _28101) : (term34 _28101 q) = (term35 _28101 q).
Proof. exact (MK_COMB (@lem1202230 _28101) (@lem1202229 _28101 q)). Qed.
Lemma lem1202236 {_28101 : Type'} (q : list _28101) : (term36 _28101 q) = (term36 _28101 q).
Proof. exact (eq_refl (term36 _28101 q)). Qed.
Lemma lem1202237 {_28101 : Type'} (q : list _28101) : ((term33 _28101 q) = (term36 _28101 q)) = ((@LAST _28101 q) = (term36 _28101 q)).
Proof. exact (MK_COMB (@lem1202231 _28101 q) (@lem1202236 _28101 q)). Qed.
Lemma lem1202240 {_28101 : Type'} : (term37 _28101) = (term38 _28101).
Proof. exact (fun_ext (fun q : list _28101 => @lem1202237 _28101 q)). Qed.
Lemma lem1202241 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202242 {_28101 : Type'} : (term4 _28101) = (term39 _28101).
Proof. exact (MK_COMB (@lem1202241 _28101) (@lem1202240 _28101)). Qed.
Lemma lem1202247 {_28101 : Type'} : (term39 _28101) = (term4 _28101).
Proof. exact (SYM (@lem1202242 _28101)). Qed.
Lemma lem1202248 {_27653 : Type'} (l : list _27653) : term40 _27653 l.
Proof. exact (@lem1187397 _27653 l). Qed.
Lemma lem1202249 {_27653 : Type'} (l : list _27653) : (term40 _27653 l) = (term41 _27653 l).
Proof. exact (eq_refl (term40 _27653 l)). Qed.
Lemma lem1202250 {_27653 : Type'} (l : list _27653) : term41 _27653 l.
Proof. exact (EQ_MP (@lem1202249 _27653 l) (@lem1202248 _27653 l)). Qed.
Lemma lem1202251 {_27653 : Type'} (l : list _27653) (m : list _27653) : term42 _27653 l m.
Proof. exact (@lem1202250 _27653 l m). Qed.
Lemma lem1202252 {_27653 : Type'} (l : list _27653) (m : list _27653) : (term42 _27653 l m) = (((@List.app _27653 l m) = (@nil _27653)) = (term43 _27653 l m)).
Proof. exact (eq_refl (term42 _27653 l m)). Qed.
Lemma lem1202254 {A : Type'} : term44 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1202255 {A : Type'} (h : A) : term45 A h.
Proof. exact (@lem1202254 A h). Qed.
Lemma lem1202256 {A : Type'} (h : A) : (term45 A h) = (term46 A h).
Proof. exact (eq_refl (term45 A h)). Qed.
Lemma lem1202257 {A : Type'} (h : A) : term46 A h.
Proof. exact (EQ_MP (@lem1202256 A h) (@lem1202255 A h)). Qed.
Lemma lem1202258 {A : Type'} (h : A) (t : list A) : term47 A h t.
Proof. exact (@lem1202257 A h t). Qed.
Lemma lem1202259 {A : Type'} (h : A) (t : list A) : (term47 A h t) = (term48 A h t).
Proof. exact (eq_refl (term47 A h t)). Qed.
Lemma lem1202260 {A : Type'} (h : A) (t : list A) : term48 A h t.
Proof. exact (EQ_MP (@lem1202259 A h t) (@lem1202258 A h t)). Qed.
Lemma lem1202261 {A : Type'} (h : A) (t : list A) (l : list A) : term49 A h t l.
Proof. exact (@lem1202260 A h t l). Qed.
Lemma lem1202262 {A : Type'} (h : A) (t : list A) (l : list A) : (term49 A h t l) = ((term50 A h t l) = (term51 A h t l)).
Proof. exact (eq_refl (term49 A h t l)). Qed.
Lemma lem1202268 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : term52 _28101 t q.
Proof. exact (@lem1202197 _28101 t h1 q). Qed.
Lemma lem1202269 {_28101 : Type'} (t : list _28101) (q : list _28101) : (term52 _28101 t q) = ((term53 _28101 t q) = (term54 _28101 t q)).
Proof. exact (eq_refl (term52 _28101 t q)). Qed.
Lemma lem1202278 {A : Type'} (h : A) (t : list A) (l : list A) : (term50 A h t l) = (term51 A h t l).
Proof. exact (EQ_MP (@lem1202262 A h t l) (@lem1202261 A h t l)). Qed.
Lemma lem1202279 {_28101 : Type'} (h : _28101) (t : list _28101) (l : list _28101) : (term50 _28101 h t l) = (term51 _28101 h t l).
Proof. exact (@lem1202278 _28101 h t l). Qed.
Lemma lem1202280 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) : (term50 _28101 h t q) = (term51 _28101 h t q).
Proof. exact (@lem1202279 _28101 h t q). Qed.
Lemma lem1202281 {_28101 : Type'} : (@LAST _28101) = (@LAST _28101).
Proof. exact (eq_refl (@LAST _28101)). Qed.
Lemma lem1202282 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) : (term55 _28101 h t q) = (term56 _28101 h t q).
Proof. exact (MK_COMB (@lem1202281 _28101) (@lem1202280 _28101 h t q)). Qed.
Lemma lem1202284 {A : Type'} (h : A) (t : list A) : (term57 A h t) = (term58 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1202285 {_28101 : Type'} (h : _28101) (t : list _28101) : (term57 _28101 h t) = (term58 _28101 h t).
Proof. exact (@lem1202284 _28101 h t). Qed.
Lemma lem1202286 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) : (term56 _28101 h t q) = (term59 _28101 h t q).
Proof. exact (@lem1202285 _28101 h (@List.app _28101 t q)). Qed.
Lemma lem1202290 {_27653 : Type'} (l : list _27653) (m : list _27653) : ((@List.app _27653 l m) = (@nil _27653)) = (term43 _27653 l m).
Proof. exact (EQ_MP (@lem1202252 _27653 l m) (@lem1202251 _27653 l m)). Qed.
Lemma lem1202291 {_28101 : Type'} (l : list _28101) (m : list _28101) : ((@List.app _28101 l m) = (@nil _28101)) = (term43 _28101 l m).
Proof. exact (@lem1202290 _28101 l m). Qed.
Lemma lem1202292 {_28101 : Type'} (t : list _28101) (q : list _28101) : ((@List.app _28101 t q) = (@nil _28101)) = (term43 _28101 t q).
Proof. exact (@lem1202291 _28101 t q). Qed.
Lemma lem1202299 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202300 {_28101 : Type'} (t : list _28101) (q : list _28101) : (term60 _28101 t q) = (term61 _28101 t q).
Proof. exact (MK_COMB (@lem1202299 _28101) (@lem1202292 _28101 t q)). Qed.
Lemma lem1202301 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202302 {_28101 : Type'} (t : list _28101) (q : list _28101) (h : _28101) : (term62 _28101 t q h) = (term63 _28101 t q h).
Proof. exact (MK_COMB (@lem1202300 _28101 t q) (@lem1202301 _28101 h)). Qed.
Lemma lem1202304 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : (term53 _28101 t q) = (term54 _28101 t q).
Proof. exact (EQ_MP (@lem1202269 _28101 t q) (@lem1202268 _28101 q t h1)). Qed.
Lemma lem1202305 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : (term53 _28101 t q) = (term54 _28101 t q).
Proof. exact (@lem1202304 _28101 q t h1). Qed.
Lemma lem1202310 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : (term59 _28101 h t q) = (term64 _28101 h t q).
Proof. exact (MK_COMB (@lem1202302 _28101 t q h) (@lem1202305 _28101 q t h1)). Qed.
Lemma lem1202311 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : (term56 _28101 h t q) = (term64 _28101 h t q).
Proof. exact (TRANS (@lem1202286 _28101 h t q) (@lem1202310 _28101 h q t h1)). Qed.
Lemma lem1202312 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : (term55 _28101 h t q) = (term64 _28101 h t q).
Proof. exact (TRANS (@lem1202282 _28101 h t q) (@lem1202311 _28101 h q t h1)). Qed.
Lemma lem1202313 {_28101 : Type'} : (@eq _28101) = (@eq _28101).
Proof. exact (eq_refl (@eq _28101)). Qed.
Lemma lem1202314 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : (term65 _28101 h t q) = (term66 _28101 h t q).
Proof. exact (MK_COMB (@lem1202313 _28101) (@lem1202312 _28101 h q t h1)). Qed.
Lemma lem1202320 {A : Type'} (h : A) (t : list A) : (term57 A h t) = (term58 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
Lemma lem1202321 {_28101 : Type'} (h : _28101) (t : list _28101) : (term57 _28101 h t) = (term58 _28101 h t).
Proof. exact (@lem1202320 _28101 h t). Qed.
Lemma lem1202326 {_28101 : Type'} (q : list _28101) : (term67 _28101 q) = (term67 _28101 q).
Proof. exact (eq_refl (term67 _28101 q)). Qed.
Lemma lem1202327 {_28101 : Type'} (q : list _28101) (h : _28101) (t : list _28101) : (term68 _28101 q h t) = (term69 _28101 q h t).
Proof. exact (MK_COMB (@lem1202326 _28101 q) (@lem1202321 _28101 h t)). Qed.
Lemma lem1202328 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202329 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) : (term70 _28101 h t q) = (term71 _28101 h t q).
Proof. exact (MK_COMB (@lem1202327 _28101 q h t) (@lem1202328 _28101 q)). Qed.
Lemma lem1202332 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : term8 _28101 t) : ((term55 _28101 h t q) = (term70 _28101 h t q)) = ((term64 _28101 h t q) = (term71 _28101 h t q)).
Proof. exact (MK_COMB (@lem1202314 _28101 h q t h1) (@lem1202329 _28101 h t q)). Qed.
Lemma lem1202335 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term8 _28101 t) : (term72 _28101 h t) = (term73 _28101 h t).
Proof. exact (fun_ext (fun q : list _28101 => @lem1202332 _28101 h q t h1)). Qed.
Lemma lem1202336 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202337 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term8 _28101 t) : (term12 _28101 h t) = (term74 _28101 h t).
Proof. exact (MK_COMB (@lem1202336 _28101) (@lem1202335 _28101 h t h1)). Qed.
Lemma lem1202342 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term8 _28101 t) : (term74 _28101 h t) = (term12 _28101 h t).
Proof. exact (SYM (@lem1202337 _28101 h t h1)). Qed.
Lemma lem1202344 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1202345 {_28101 : Type'} : (term39 _28101) = (term76 _28101).
Proof. exact (@lem1202344 (term39 _28101)). Qed.
Lemma lem1202346 {_28101 : Type'} : (term76 _28101) = (term39 _28101).
Proof. exact (SYM (@lem1202345 _28101)). Qed.
Lemma lem1202347 {_28101 : Type'} (h1 : term77 _28101) : term77 _28101.
Proof. exact (h1). Qed.
Lemma lem1202350 {_28101 : Type'} (h1 : term76 _28101) : term76 _28101.
Proof. exact (h1). Qed.
Lemma lem1202351 {_28101 : Type'} : term78 _28101.
Proof. exact (fun h0 : term76 _28101 => @lem1202350 _28101 h0). Qed.
Lemma lem1202352 {_28101 : Type'} (h1 : term78 _28101) : term78 _28101.
Proof. exact (h1). Qed.
Lemma lem1202353 {_28101 : Type'} (h1 : term76 _28101) : term76 _28101.
Proof. exact (h1). Qed.
Lemma lem1202354 {_28101 : Type'} (h1 : term76 _28101) (h2 : term78 _28101) : term76 _28101.
Proof. exact (@lem1202352 _28101 h2 (@lem1202353 _28101 h1)). Qed.
Lemma lem1202355 {_28101 : Type'} (h1 : term76 _28101) : term79 _28101.
Proof. exact (fun h0 : term78 _28101 => @lem1202354 _28101 h1 h0). Qed.
Lemma lem1202356 {_28101 : Type'} (h1 : term78 _28101) : term78 _28101.
Proof. exact (h1). Qed.
Lemma lem1202357 {_28101 : Type'} (h1 : term76 _28101) (h2 : term78 _28101) : term76 _28101.
Proof. exact (@lem1202355 _28101 h1 (@lem1202356 _28101 h2)). Qed.
Lemma lem1202358 {_28101 : Type'} (h1 : term78 _28101) : term78 _28101.
Proof. exact (fun h0 : term76 _28101 => @lem1202357 _28101 h0 h1). Qed.
Lemma lem1202359 {_28101 : Type'} : term80 _28101.
Proof. exact (fun h0 : term78 _28101 => @lem1202358 _28101 h0). Qed.
Lemma lem1202362 {_28101 : Type'} : term78 _28101.
Proof. exact (@lem1202359 _28101 (@lem1202351 _28101)). Qed.
Lemma lem1202363 {_28101 : Type'} : term78 _28101.
Proof. exact (@lem1202362 _28101). Qed.
Lemma lem1202365 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1202366 {_28101 : Type'} : (term76 _28101) = (term81 _28101).
Proof. exact (@lem1202365 (term77 _28101)). Qed.
Lemma lem1202368 (t : Prop) : (term82 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1202369 {_28101 : Type'} : (term81 _28101) = (term39 _28101).
Proof. exact (@lem1202368 (term39 _28101)). Qed.
Lemma lem1202378 {_28101 : Type'} : (term76 _28101) = (term39 _28101).
Proof. exact (TRANS (@lem1202366 _28101) (@lem1202369 _28101)). Qed.
Lemma lem1202382 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (q = (@nil _28101)) = False.
Proof. exact (h1). Qed.
Lemma lem1202383 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202384 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term67 _28101 q) = (@COND _28101 False).
Proof. exact (MK_COMB (@lem1202383 _28101) (@lem1202382 _28101 q h1)). Qed.
Lemma lem1202385 {_28101 : Type'} : (@LAST _28101 (@nil _28101)) = (@LAST _28101 (@nil _28101)).
Proof. exact (eq_refl (@LAST _28101 (@nil _28101))). Qed.
Lemma lem1202386 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term83 _28101 q) = (term84 _28101).
Proof. exact (MK_COMB (@lem1202384 _28101 q h1) (@lem1202385 _28101)). Qed.
Lemma lem1202387 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202388 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term36 _28101 q) = (term85 _28101 q).
Proof. exact (MK_COMB (@lem1202386 _28101 q h1) (@lem1202387 _28101 q)). Qed.
Lemma lem1202390 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1202391 {_28101 : Type'} (t1 : _28101) (t2 : _28101) : (@COND _28101 False t1 t2) = t2.
Proof. exact (@lem1202390 _28101 t1 t2). Qed.
Lemma lem1202392 {_28101 : Type'} (q : list _28101) : (term85 _28101 q) = (@LAST _28101 q).
Proof. exact (@lem1202391 _28101 (@LAST _28101 (@nil _28101)) (@LAST _28101 q)). Qed.
Lemma lem1202393 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term36 _28101 q) = (@LAST _28101 q).
Proof. exact (TRANS (@lem1202388 _28101 q h1) (@lem1202392 _28101 q)). Qed.
Lemma lem1202394 {_28101 : Type'} (q : list _28101) : (term35 _28101 q) = (term35 _28101 q).
Proof. exact (eq_refl (term35 _28101 q)). Qed.
Lemma lem1202395 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : ((@LAST _28101 q) = (term36 _28101 q)) = ((@LAST _28101 q) = (@LAST _28101 q)).
Proof. exact (MK_COMB (@lem1202394 _28101 q) (@lem1202393 _28101 q h1)). Qed.
Lemma lem1202397 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1202398 {_28101 : Type'} (x : _28101) : (x = x) = True.
Proof. exact (@lem1202397 _28101 x). Qed.
Lemma lem1202399 {_28101 : Type'} (q : list _28101) : ((@LAST _28101 q) = (@LAST _28101 q)) = True.
Proof. exact (@lem1202398 _28101 (@LAST _28101 q)). Qed.
Lemma lem1202400 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : ((@LAST _28101 q) = (term36 _28101 q)) = True.
Proof. exact (TRANS (@lem1202395 _28101 q h1) (@lem1202399 _28101 q)). Qed.
Lemma lem1202401 {_28101 : Type'} (q : list _28101) : term86 _28101 q.
Proof. exact (fun h0 : (q = (@nil _28101)) = False => @lem1202400 _28101 q h0). Qed.
Lemma lem1202403 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (q = (@nil _28101)) = True.
Proof. exact (h1). Qed.
Lemma lem1202404 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202405 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term67 _28101 q) = (@COND _28101 True).
Proof. exact (MK_COMB (@lem1202404 _28101) (@lem1202403 _28101 q h1)). Qed.
Lemma lem1202406 {_28101 : Type'} : (@LAST _28101 (@nil _28101)) = (@LAST _28101 (@nil _28101)).
Proof. exact (eq_refl (@LAST _28101 (@nil _28101))). Qed.
Lemma lem1202407 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term83 _28101 q) = (term87 _28101).
Proof. exact (MK_COMB (@lem1202405 _28101 q h1) (@lem1202406 _28101)). Qed.
Lemma lem1202408 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202409 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term36 _28101 q) = (term88 _28101 q).
Proof. exact (MK_COMB (@lem1202407 _28101 q h1) (@lem1202408 _28101 q)). Qed.
Lemma lem1202411 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1202412 {_28101 : Type'} (t2 : _28101) (t1 : _28101) : (@COND _28101 True t1 t2) = t1.
Proof. exact (@lem1202411 _28101 t2 t1). Qed.
Lemma lem1202413 {_28101 : Type'} (q : list _28101) : (term88 _28101 q) = (@LAST _28101 (@nil _28101)).
Proof. exact (@lem1202412 _28101 (@LAST _28101 q) (@LAST _28101 (@nil _28101))). Qed.
Lemma lem1202414 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term36 _28101 q) = (@LAST _28101 (@nil _28101)).
Proof. exact (TRANS (@lem1202409 _28101 q h1) (@lem1202413 _28101 q)). Qed.
Lemma lem1202415 {_28101 : Type'} (q : list _28101) : (term35 _28101 q) = (term35 _28101 q).
Proof. exact (eq_refl (term35 _28101 q)). Qed.
Lemma lem1202416 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : ((@LAST _28101 q) = (term36 _28101 q)) = ((@LAST _28101 q) = (@LAST _28101 (@nil _28101))).
Proof. exact (MK_COMB (@lem1202415 _28101 q) (@lem1202414 _28101 q h1)). Qed.
Lemma lem1202419 {_28101 : Type'} (q : list _28101) : term89 _28101 q.
Proof. exact (fun h0 : (q = (@nil _28101)) = True => @lem1202416 _28101 q h0). Qed.
Lemma lem1202420 {_28101 : Type'} (q : list _28101) : term90 _28101 q.
Proof. exact (conj (@lem1202401 _28101 q) (@lem1202419 _28101 q)). Qed.
Lemma lem1202422 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term91 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1202423 {_28101 : Type'} (q : list _28101) : term92 _28101 q.
Proof. exact (@lem1202422 ((@LAST _28101 q) = (term36 _28101 q)) ((@LAST _28101 q) = (@LAST _28101 (@nil _28101))) (q = (@nil _28101)) True). Qed.
Lemma lem1202424 {_28101 : Type'} (q : list _28101) : ((@LAST _28101 q) = (term36 _28101 q)) = (term93 _28101 q).
Proof. exact (@lem1202423 _28101 q (@lem1202420 _28101 q)). Qed.
Lemma lem1202426 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1202427 {_28101 : Type'} (q : list _28101) : (term94 _28101 q) = True.
Proof. exact (@lem1202426 (q = (@nil _28101))). Qed.
Lemma lem1202432 {_28101 : Type'} (q : list _28101) : (term95 _28101 q) = (term95 _28101 q).
Proof. exact (eq_refl (term95 _28101 q)). Qed.
Lemma lem1202433 {_28101 : Type'} (q : list _28101) : (term93 _28101 q) = (term96 _28101 q).
Proof. exact (MK_COMB (@lem1202432 _28101 q) (@lem1202427 _28101 q)). Qed.
Lemma lem1202435 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1202436 {_28101 : Type'} (q : list _28101) : (term96 _28101 q) = (term97 _28101 q).
Proof. exact (@lem1202435 (term97 _28101 q)). Qed.
Lemma lem1202437 {_28101 : Type'} (q : list _28101) : (term93 _28101 q) = (term97 _28101 q).
Proof. exact (TRANS (@lem1202433 _28101 q) (@lem1202436 _28101 q)). Qed.
Lemma lem1202448 {_28101 : Type'} (q : list _28101) : ((@LAST _28101 q) = (term36 _28101 q)) = (term97 _28101 q).
Proof. exact (TRANS (@lem1202424 _28101 q) (@lem1202437 _28101 q)). Qed.
Lemma lem1202449 {_28101 : Type'} : (term38 _28101) = (term98 _28101).
Proof. exact (fun_ext (fun q : list _28101 => @lem1202448 _28101 q)). Qed.
Lemma lem1202450 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202451 {_28101 : Type'} : (term39 _28101) = (term99 _28101).
Proof. exact (MK_COMB (@lem1202450 _28101) (@lem1202449 _28101)). Qed.
Lemma lem1202462 {_28101 : Type'} : (term76 _28101) = (term99 _28101).
Proof. exact (TRANS (@lem1202378 _28101) (@lem1202451 _28101)). Qed.
Lemma lem1202463 {_28101 : Type'} : (term99 _28101) = (term76 _28101).
Proof. exact (SYM (@lem1202462 _28101)). Qed.
Lemma lem1202465 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1202466 {_28101 : Type'} (q : list _28101) : (term97 _28101 q) = (term100 _28101 q).
Proof. exact (@lem1202465 (term97 _28101 q)). Qed.
Lemma lem1202467 {_28101 : Type'} (q : list _28101) : (term100 _28101 q) = (term97 _28101 q).
Proof. exact (SYM (@lem1202466 _28101 q)). Qed.
Lemma lem1202468 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : term101 _28101 q.
Proof. exact (h1). Qed.
Lemma lem1202471 {_28101 : Type'} (q : list _28101) : (term102 _28101 q) = (q = (@nil _28101)).
Proof. exact (@lem16933 (q = (@nil _28101))). Qed.
Lemma lem1202472 {_28101 : Type'} (q : list _28101) : (term103 _28101 q) = (term103 _28101 q).
Proof. exact (eq_refl (term103 _28101 q)). Qed.
Lemma lem1202473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1202474 {_28101 : Type'} (q : list _28101) : (term104 _28101 q) = (term105 _28101 q).
Proof. exact (MK_COMB (@lem1202473) (@lem1202471 _28101 q)). Qed.
Lemma lem1202475 {_28101 : Type'} (q : list _28101) : (term106 _28101 q) = (term107 _28101 q).
Proof. exact (MK_COMB (@lem1202474 _28101 q) (@lem1202472 _28101 q)). Qed.
Lemma lem1202476 {_28101 : Type'} (q : list _28101) : (term101 _28101 q) = (term106 _28101 q).
Proof. exact (@lem17160 (term108 _28101 q) ((@LAST _28101 q) = (@LAST _28101 (@nil _28101)))). Qed.
Lemma lem1202481 {_28101 : Type'} (q : list _28101) : (term101 _28101 q) = (term107 _28101 q).
Proof. exact (TRANS (@lem1202476 _28101 q) (@lem1202475 _28101 q)). Qed.
Lemma lem1202502 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : term107 _28101 q.
Proof. exact (EQ_MP (@lem1202481 _28101 q) (@lem1202468 _28101 q h1)). Qed.
Lemma lem1202514 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : q = (@nil _28101).
Proof. exact (proj1 (@lem1202502 _28101 q h1)). Qed.
Lemma lem1202516 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : term103 _28101 q.
Proof. exact (proj2 (@lem1202502 _28101 q h1)). Qed.
Lemma lem1202531 {_28101 : Type'} : (term109 _28101) = (term109 _28101).
Proof. exact (eq_refl (term109 _28101)). Qed.
Lemma lem1202532 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : (term110 _28101 q) = (term111 _28101).
Proof. exact (MK_COMB (@lem1202531 _28101) (@lem1202514 _28101 q h1)). Qed.
Lemma lem1202533 {_28101 : Type'} : (term111 _28101) = (term112 _28101).
Proof. exact (eq_refl (term111 _28101)). Qed.
Lemma lem1202534 {_28101 : Type'} (q : list _28101) : (term113 _28101 q) = (term113 _28101 q).
Proof. exact (eq_refl (term113 _28101 q)). Qed.
Lemma lem1202535 {_28101 : Type'} (q : list _28101) : ((term110 _28101 q) = (term111 _28101)) = ((term110 _28101 q) = (term112 _28101)).
Proof. exact (MK_COMB (@lem1202534 _28101 q) (@lem1202533 _28101)). Qed.
Lemma lem1202536 {_28101 : Type'} (q : list _28101) : (term110 _28101 q) = (term103 _28101 q).
Proof. exact (eq_refl (term110 _28101 q)). Qed.
Lemma lem1202537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1202538 {_28101 : Type'} (q : list _28101) : (term113 _28101 q) = (term114 _28101 q).
Proof. exact (MK_COMB (@lem1202537) (@lem1202536 _28101 q)). Qed.
Lemma lem1202539 {_28101 : Type'} : (term112 _28101) = (term112 _28101).
Proof. exact (eq_refl (term112 _28101)). Qed.
Lemma lem1202540 {_28101 : Type'} (q : list _28101) : ((term110 _28101 q) = (term112 _28101)) = ((term103 _28101 q) = (term112 _28101)).
Proof. exact (MK_COMB (@lem1202538 _28101 q) (@lem1202539 _28101)). Qed.
Lemma lem1202541 {_28101 : Type'} (q : list _28101) : ((term110 _28101 q) = (term111 _28101)) = ((term103 _28101 q) = (term112 _28101)).
Proof. exact (TRANS (@lem1202535 _28101 q) (@lem1202540 _28101 q)). Qed.
Lemma lem1202542 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : (term103 _28101 q) = (term112 _28101).
Proof. exact (EQ_MP (@lem1202541 _28101 q) (@lem1202532 _28101 q h1)). Qed.
Lemma lem1202543 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : term112 _28101.
Proof. exact (EQ_MP (@lem1202542 _28101 q h1) (@lem1202516 _28101 q h1)). Qed.
Lemma lem1202557 {_28101 : Type'} (x : _28101) : x = x.
Proof. exact (@lem21386 _28101 x). Qed.
Lemma lem1202558 {_28101 : Type'} (x : _28101) : x = x.
Proof. exact (@lem1202557 _28101 x). Qed.
Lemma lem1202559 {_28101 : Type'} : (@LAST _28101 (@nil _28101)) = (@LAST _28101 (@nil _28101)).
Proof. exact (@lem1202558 _28101 (@LAST _28101 (@nil _28101))). Qed.
Lemma lem1202560 {_28101 : Type'} : term115 _28101.
Proof. exact (fun h0 : term112 _28101 => @lem1202559 _28101). Qed.
Lemma lem1202562 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1202563 {_28101 : Type'} : (term115 _28101) = ((@LAST _28101 (@nil _28101)) = (@LAST _28101 (@nil _28101))).
Proof. exact (@lem1202562 ((@LAST _28101 (@nil _28101)) = (@LAST _28101 (@nil _28101)))). Qed.
Lemma lem1202564 {_28101 : Type'} : (@LAST _28101 (@nil _28101)) = (@LAST _28101 (@nil _28101)).
Proof. exact (EQ_MP (@lem1202563 _28101) (@lem1202560 _28101)). Qed.
Lemma lem1202567 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1202569 {_28101 : Type'} : (term112 _28101) = (term117 _28101).
Proof. exact (@lem1202567 ((@LAST _28101 (@nil _28101)) = (@LAST _28101 (@nil _28101)))). Qed.
Lemma lem1202572 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : term117 _28101.
Proof. exact (EQ_MP (@lem1202569 _28101) (@lem1202543 _28101 q h1)). Qed.
Lemma lem1202575 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : False.
Proof. exact (@lem1202572 _28101 q h1 (@lem1202564 _28101)). Qed.
Lemma lem1202576 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : term118.
Proof. exact (fun h0 : ~ False => @lem1202575 _28101 q h1). Qed.
Lemma lem1202578 (p : Prop) : (term116 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1202579 : term118 = False.
Proof. exact (@lem1202578 False). Qed.
Lemma lem1202581 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : False.
Proof. exact (EQ_MP (@lem1202579) (@lem1202576 _28101 q h1)). Qed.
Lemma lem1202582 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : (term101 _28101 q) = False.
Proof. exact (prop_ext (fun h2 : term101 _28101 q => @lem1202581 _28101 q h1) (fun h2 : False => @lem1202468 _28101 q h1)). Qed.
Lemma lem1202583 {_28101 : Type'} (q : list _28101) (h1 : term101 _28101 q) : False.
Proof. exact (EQ_MP (@lem1202582 _28101 q h1) (@lem1202468 _28101 q h1)). Qed.
Lemma lem1202584 {_28101 : Type'} (q : list _28101) : term100 _28101 q.
Proof. exact (fun h0 : term101 _28101 q => @lem1202583 _28101 q h0). Qed.
Lemma lem1202585 {_28101 : Type'} (q : list _28101) : term97 _28101 q.
Proof. exact (EQ_MP (@lem1202467 _28101 q) (@lem1202584 _28101 q)). Qed.
Lemma lem1202590 {_28101 : Type'} : term99 _28101.
Proof. exact (fun q : list _28101 => @lem1202585 _28101 q). Qed.
Lemma lem1202591 {_28101 : Type'} : term76 _28101.
Proof. exact (EQ_MP (@lem1202463 _28101) (@lem1202590 _28101)). Qed.
Lemma lem1202593 {_28101 : Type'} : term76 _28101.
Proof. exact (@lem1202363 _28101 (@lem1202591 _28101)). Qed.
Lemma lem1202594 {_28101 : Type'} (h1 : term77 _28101) : False.
Proof. exact (@lem1202593 _28101 (@lem1202347 _28101 h1)). Qed.
Lemma lem1202595 {_28101 : Type'} (h1 : term77 _28101) : (term77 _28101) = False.
Proof. exact (prop_ext (fun h2 : term77 _28101 => @lem1202594 _28101 h1) (fun h2 : False => @lem1202347 _28101 h1)). Qed.
Lemma lem1202596 {_28101 : Type'} (h1 : term77 _28101) : False.
Proof. exact (EQ_MP (@lem1202595 _28101 h1) (@lem1202347 _28101 h1)). Qed.
Lemma lem1202597 {_28101 : Type'} : term76 _28101.
Proof. exact (fun h0 : term77 _28101 => @lem1202596 _28101 h0). Qed.
Lemma lem1202598 {_28101 : Type'} : term39 _28101.
Proof. exact (EQ_MP (@lem1202346 _28101) (@lem1202597 _28101)). Qed.
Lemma lem1202600 (p : Prop) : p = (term75 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1202601 {_28101 : Type'} (h : _28101) (t : list _28101) : (term74 _28101 h t) = (term119 _28101 h t).
Proof. exact (@lem1202600 (term74 _28101 h t)). Qed.
Lemma lem1202602 {_28101 : Type'} (h : _28101) (t : list _28101) : (term119 _28101 h t) = (term74 _28101 h t).
Proof. exact (SYM (@lem1202601 _28101 h t)). Qed.
Lemma lem1202603 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term120 _28101 h t) : term120 _28101 h t.
Proof. exact (h1). Qed.
Lemma lem1202606 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term119 _28101 h t) : term119 _28101 h t.
Proof. exact (h1). Qed.
Lemma lem1202607 {_28101 : Type'} (h : _28101) (t : list _28101) : term121 _28101 h t.
Proof. exact (fun h0 : term119 _28101 h t => @lem1202606 _28101 h t h0). Qed.
Lemma lem1202608 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term121 _28101 h t) : term121 _28101 h t.
Proof. exact (h1). Qed.
Lemma lem1202609 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term119 _28101 h t) : term119 _28101 h t.
Proof. exact (h1). Qed.
Lemma lem1202610 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term119 _28101 h t) (h2 : term121 _28101 h t) : term119 _28101 h t.
Proof. exact (@lem1202608 _28101 h t h2 (@lem1202609 _28101 h t h1)). Qed.
Lemma lem1202611 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term119 _28101 h t) : term122 _28101 h t.
Proof. exact (fun h0 : term121 _28101 h t => @lem1202610 _28101 h t h1 h0). Qed.
Lemma lem1202612 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term121 _28101 h t) : term121 _28101 h t.
Proof. exact (h1). Qed.
Lemma lem1202613 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term119 _28101 h t) (h2 : term121 _28101 h t) : term119 _28101 h t.
Proof. exact (@lem1202611 _28101 h t h1 (@lem1202612 _28101 h t h2)). Qed.
Lemma lem1202614 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term121 _28101 h t) : term121 _28101 h t.
Proof. exact (fun h0 : term119 _28101 h t => @lem1202613 _28101 h t h0 h1). Qed.
Lemma lem1202615 {_28101 : Type'} (h : _28101) (t : list _28101) : term123 _28101 h t.
Proof. exact (fun h0 : term121 _28101 h t => @lem1202614 _28101 h t h0). Qed.
Lemma lem1202618 {_28101 : Type'} (h : _28101) (t : list _28101) : term121 _28101 h t.
Proof. exact (@lem1202615 _28101 h t (@lem1202607 _28101 h t)). Qed.
Lemma lem1202619 {_28101 : Type'} (h : _28101) (t : list _28101) : term121 _28101 h t.
Proof. exact (@lem1202618 _28101 h t). Qed.
Lemma lem1202629 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1202630 {_28101 : Type'} (h : _28101) (t : list _28101) : (term119 _28101 h t) = (term124 _28101 h t).
Proof. exact (@lem1202629 (term120 _28101 h t)). Qed.
Lemma lem1202632 (t : Prop) : (term82 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1202633 {_28101 : Type'} (h : _28101) (t : list _28101) : (term124 _28101 h t) = (term74 _28101 h t).
Proof. exact (@lem1202632 (term74 _28101 h t)). Qed.
Lemma lem1202638 {_28101 : Type'} (h : _28101) (t : list _28101) : (term119 _28101 h t) = (term74 _28101 h t).
Proof. exact (TRANS (@lem1202630 _28101 h t) (@lem1202633 _28101 h t)). Qed.
Lemma lem1202641 {_28101 : Type'} (t : list _28101) : (term125 _28101 t) = (term126 _28101 t).
Proof. exact (fun_ext (fun h : _28101 => @lem1202638 _28101 h t)). Qed.
Lemma lem1202642 {_28101 : Type'} : (@all _28101) = (@all _28101).
Proof. exact (eq_refl (@all _28101)). Qed.
Lemma lem1202643 {_28101 : Type'} (t : list _28101) : (term127 _28101 t) = (term128 _28101 t).
Proof. exact (MK_COMB (@lem1202642 _28101) (@lem1202641 _28101 t)). Qed.
Lemma lem1202648 {_28101 : Type'} : (term129 _28101) = (term130 _28101).
Proof. exact (fun_ext (fun t : list _28101 => @lem1202643 _28101 t)). Qed.
Lemma lem1202649 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202658 {_28101 : Type'} : (term131 _28101) = (term132 _28101).
Proof. exact (MK_COMB (@lem1202649 _28101) (@lem1202648 _28101)). Qed.
Lemma lem1202662 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (t = (@nil _28101)) = False.
Proof. exact (h1). Qed.
Lemma lem1202663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1202664 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term105 _28101 t) = (and False).
Proof. exact (MK_COMB (@lem1202663) (@lem1202662 _28101 t h1)). Qed.
Lemma lem1202667 {_28101 : Type'} (q : list _28101) : (q = (@nil _28101)) = (q = (@nil _28101)).
Proof. exact (eq_refl (q = (@nil _28101))). Qed.
Lemma lem1202668 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term43 _28101 t q) = (term133 _28101 q).
Proof. exact (MK_COMB (@lem1202664 _28101 t h1) (@lem1202667 _28101 q)). Qed.
Lemma lem1202670 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1202671 {_28101 : Type'} (q : list _28101) : (term133 _28101 q) = False.
Proof. exact (@lem1202670 (q = (@nil _28101))). Qed.
Lemma lem1202672 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term43 _28101 t q) = False.
Proof. exact (TRANS (@lem1202668 _28101 q t h1) (@lem1202671 _28101 q)). Qed.
Lemma lem1202673 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202674 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term61 _28101 t q) = (@COND _28101 False).
Proof. exact (MK_COMB (@lem1202673 _28101) (@lem1202672 _28101 q t h1)). Qed.
Lemma lem1202675 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202676 {_28101 : Type'} (q : list _28101) (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term63 _28101 t q h) = (@COND _28101 False h).
Proof. exact (MK_COMB (@lem1202674 _28101 q t h1) (@lem1202675 _28101 h)). Qed.
Lemma lem1202681 {_28101 : Type'} (t : list _28101) (q : list _28101) : (term54 _28101 t q) = (term54 _28101 t q).
Proof. exact (eq_refl (term54 _28101 t q)). Qed.
Lemma lem1202682 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term64 _28101 h t q) = (term134 _28101 h t q).
Proof. exact (MK_COMB (@lem1202676 _28101 q h t h1) (@lem1202681 _28101 t q)). Qed.
Lemma lem1202684 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1202685 {_28101 : Type'} (t1 : _28101) (t2 : _28101) : (@COND _28101 False t1 t2) = t2.
Proof. exact (@lem1202684 _28101 t1 t2). Qed.
Lemma lem1202686 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) : (term134 _28101 h t q) = (term54 _28101 t q).
Proof. exact (@lem1202685 _28101 h (term54 _28101 t q)). Qed.
Lemma lem1202689 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term64 _28101 h t q) = (term54 _28101 t q).
Proof. exact (TRANS (@lem1202682 _28101 h q t h1) (@lem1202686 _28101 h t q)). Qed.
Lemma lem1202690 {_28101 : Type'} : (@eq _28101) = (@eq _28101).
Proof. exact (eq_refl (@eq _28101)). Qed.
Lemma lem1202691 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term66 _28101 h t q) = (term135 _28101 t q).
Proof. exact (MK_COMB (@lem1202690 _28101) (@lem1202689 _28101 h q t h1)). Qed.
Lemma lem1202695 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (t = (@nil _28101)) = False.
Proof. exact (h1). Qed.
Lemma lem1202696 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202697 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term67 _28101 t) = (@COND _28101 False).
Proof. exact (MK_COMB (@lem1202696 _28101) (@lem1202695 _28101 t h1)). Qed.
Lemma lem1202698 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202699 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term136 _28101 t h) = (@COND _28101 False h).
Proof. exact (MK_COMB (@lem1202697 _28101 t h1) (@lem1202698 _28101 h)). Qed.
Lemma lem1202700 {_28101 : Type'} (t : list _28101) : (@LAST _28101 t) = (@LAST _28101 t).
Proof. exact (eq_refl (@LAST _28101 t)). Qed.
Lemma lem1202701 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term58 _28101 h t) = (term137 _28101 h t).
Proof. exact (MK_COMB (@lem1202699 _28101 h t h1) (@lem1202700 _28101 t)). Qed.
Lemma lem1202703 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1202704 {_28101 : Type'} (t1 : _28101) (t2 : _28101) : (@COND _28101 False t1 t2) = t2.
Proof. exact (@lem1202703 _28101 t1 t2). Qed.
Lemma lem1202705 {_28101 : Type'} (h : _28101) (t : list _28101) : (term137 _28101 h t) = (@LAST _28101 t).
Proof. exact (@lem1202704 _28101 h (@LAST _28101 t)). Qed.
Lemma lem1202706 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term58 _28101 h t) = (@LAST _28101 t).
Proof. exact (TRANS (@lem1202701 _28101 h t h1) (@lem1202705 _28101 h t)). Qed.
Lemma lem1202707 {_28101 : Type'} (q : list _28101) : (term67 _28101 q) = (term67 _28101 q).
Proof. exact (eq_refl (term67 _28101 q)). Qed.
Lemma lem1202708 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term69 _28101 q h t) = (term138 _28101 q t).
Proof. exact (MK_COMB (@lem1202707 _28101 q) (@lem1202706 _28101 h t h1)). Qed.
Lemma lem1202709 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202710 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term71 _28101 h t q) = (term54 _28101 t q).
Proof. exact (MK_COMB (@lem1202708 _28101 h q t h1) (@lem1202709 _28101 q)). Qed.
Lemma lem1202713 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : ((term64 _28101 h t q) = (term71 _28101 h t q)) = ((term54 _28101 t q) = (term54 _28101 t q)).
Proof. exact (MK_COMB (@lem1202691 _28101 h q t h1) (@lem1202710 _28101 h q t h1)). Qed.
Lemma lem1202715 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1202716 {_28101 : Type'} (x : _28101) : (x = x) = True.
Proof. exact (@lem1202715 _28101 x). Qed.
Lemma lem1202717 {_28101 : Type'} (t : list _28101) (q : list _28101) : ((term54 _28101 t q) = (term54 _28101 t q)) = True.
Proof. exact (@lem1202716 _28101 (term54 _28101 t q)). Qed.
Lemma lem1202718 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : ((term64 _28101 h t q) = (term71 _28101 h t q)) = True.
Proof. exact (TRANS (@lem1202713 _28101 h q t h1) (@lem1202717 _28101 t q)). Qed.
Lemma lem1202719 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term73 _28101 h t) = (term139 _28101).
Proof. exact (fun_ext (fun q : list _28101 => @lem1202718 _28101 h q t h1)). Qed.
Lemma lem1202720 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202721 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term74 _28101 h t) = (term140 _28101).
Proof. exact (MK_COMB (@lem1202720 _28101) (@lem1202719 _28101 h t h1)). Qed.
Lemma lem1202723 {A : Type'} (t : Prop) : (term141 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1202724 {_28101 : Type'} (t : Prop) : (term142 _28101 t) = t.
Proof. exact (@lem1202723 (list _28101) t). Qed.
Lemma lem1202725 {_28101 : Type'} : (term140 _28101) = True.
Proof. exact (@lem1202724 _28101 True). Qed.
Lemma lem1202726 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term74 _28101 h t) = True.
Proof. exact (TRANS (@lem1202721 _28101 h t h1) (@lem1202725 _28101)). Qed.
Lemma lem1202727 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term126 _28101 t) = (term143 _28101).
Proof. exact (fun_ext (fun h : _28101 => @lem1202726 _28101 h t h1)). Qed.
Lemma lem1202728 {_28101 : Type'} : (@all _28101) = (@all _28101).
Proof. exact (eq_refl (@all _28101)). Qed.
Lemma lem1202729 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term128 _28101 t) = (term144 _28101).
Proof. exact (MK_COMB (@lem1202728 _28101) (@lem1202727 _28101 t h1)). Qed.
Lemma lem1202731 {A : Type'} (t : Prop) : (term141 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1202732 {_28101 : Type'} (t : Prop) : (term141 _28101 t) = t.
Proof. exact (@lem1202731 _28101 t). Qed.
Lemma lem1202733 {_28101 : Type'} : (term144 _28101) = True.
Proof. exact (@lem1202732 _28101 True). Qed.
Lemma lem1202734 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = False) : (term128 _28101 t) = True.
Proof. exact (TRANS (@lem1202729 _28101 t h1) (@lem1202733 _28101)). Qed.
Lemma lem1202735 {_28101 : Type'} (t : list _28101) : term145 _28101 t.
Proof. exact (fun h0 : (t = (@nil _28101)) = False => @lem1202734 _28101 t h0). Qed.
Lemma lem1202737 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (t = (@nil _28101)) = True.
Proof. exact (h1). Qed.
Lemma lem1202738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1202739 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term105 _28101 t) = (and True).
Proof. exact (MK_COMB (@lem1202738) (@lem1202737 _28101 t h1)). Qed.
Lemma lem1202742 {_28101 : Type'} (q : list _28101) : (q = (@nil _28101)) = (q = (@nil _28101)).
Proof. exact (eq_refl (q = (@nil _28101))). Qed.
Lemma lem1202743 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term43 _28101 t q) = (term146 _28101 q).
Proof. exact (MK_COMB (@lem1202739 _28101 t h1) (@lem1202742 _28101 q)). Qed.
Lemma lem1202745 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1202746 {_28101 : Type'} (q : list _28101) : (term146 _28101 q) = (q = (@nil _28101)).
Proof. exact (@lem1202745 (q = (@nil _28101))). Qed.
Lemma lem1202749 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term43 _28101 t q) = (q = (@nil _28101)).
Proof. exact (TRANS (@lem1202743 _28101 q t h1) (@lem1202746 _28101 q)). Qed.
Lemma lem1202750 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202751 {_28101 : Type'} (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term61 _28101 t q) = (term67 _28101 q).
Proof. exact (MK_COMB (@lem1202750 _28101) (@lem1202749 _28101 q t h1)). Qed.
Lemma lem1202752 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202753 {_28101 : Type'} (q : list _28101) (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term63 _28101 t q h) = (term136 _28101 q h).
Proof. exact (MK_COMB (@lem1202751 _28101 q t h1) (@lem1202752 _28101 h)). Qed.
Lemma lem1202758 {_28101 : Type'} (t : list _28101) (q : list _28101) : (term54 _28101 t q) = (term54 _28101 t q).
Proof. exact (eq_refl (term54 _28101 t q)). Qed.
Lemma lem1202759 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term64 _28101 h t q) = (term147 _28101 h t q).
Proof. exact (MK_COMB (@lem1202753 _28101 q h t h1) (@lem1202758 _28101 t q)). Qed.
Lemma lem1202762 {_28101 : Type'} : (@eq _28101) = (@eq _28101).
Proof. exact (eq_refl (@eq _28101)). Qed.
Lemma lem1202763 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term66 _28101 h t q) = (term148 _28101 h t q).
Proof. exact (MK_COMB (@lem1202762 _28101) (@lem1202759 _28101 h q t h1)). Qed.
Lemma lem1202767 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (t = (@nil _28101)) = True.
Proof. exact (h1). Qed.
Lemma lem1202768 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202769 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term67 _28101 t) = (@COND _28101 True).
Proof. exact (MK_COMB (@lem1202768 _28101) (@lem1202767 _28101 t h1)). Qed.
Lemma lem1202770 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202771 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term136 _28101 t h) = (@COND _28101 True h).
Proof. exact (MK_COMB (@lem1202769 _28101 t h1) (@lem1202770 _28101 h)). Qed.
Lemma lem1202772 {_28101 : Type'} (t : list _28101) : (@LAST _28101 t) = (@LAST _28101 t).
Proof. exact (eq_refl (@LAST _28101 t)). Qed.
Lemma lem1202773 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term58 _28101 h t) = (term149 _28101 h t).
Proof. exact (MK_COMB (@lem1202771 _28101 h t h1) (@lem1202772 _28101 t)). Qed.
Lemma lem1202775 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1202776 {_28101 : Type'} (t2 : _28101) (t1 : _28101) : (@COND _28101 True t1 t2) = t1.
Proof. exact (@lem1202775 _28101 t2 t1). Qed.
Lemma lem1202777 {_28101 : Type'} (t : list _28101) (h : _28101) : (term149 _28101 h t) = h.
Proof. exact (@lem1202776 _28101 (@LAST _28101 t) h). Qed.
Lemma lem1202778 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term58 _28101 h t) = h.
Proof. exact (TRANS (@lem1202773 _28101 h t h1) (@lem1202777 _28101 t h)). Qed.
Lemma lem1202779 {_28101 : Type'} (q : list _28101) : (term67 _28101 q) = (term67 _28101 q).
Proof. exact (eq_refl (term67 _28101 q)). Qed.
Lemma lem1202780 {_28101 : Type'} (q : list _28101) (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term69 _28101 q h t) = (term136 _28101 q h).
Proof. exact (MK_COMB (@lem1202779 _28101 q) (@lem1202778 _28101 h t h1)). Qed.
Lemma lem1202781 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202782 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term71 _28101 h t q) = (term58 _28101 h q).
Proof. exact (MK_COMB (@lem1202780 _28101 q h t h1) (@lem1202781 _28101 q)). Qed.
Lemma lem1202785 {_28101 : Type'} (h : _28101) (q : list _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : ((term64 _28101 h t q) = (term71 _28101 h t q)) = ((term147 _28101 h t q) = (term58 _28101 h q)).
Proof. exact (MK_COMB (@lem1202763 _28101 h q t h1) (@lem1202782 _28101 h q t h1)). Qed.
Lemma lem1202788 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term73 _28101 h t) = (term150 _28101 t h).
Proof. exact (fun_ext (fun q : list _28101 => @lem1202785 _28101 h q t h1)). Qed.
Lemma lem1202789 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202790 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term74 _28101 h t) = (term151 _28101 t h).
Proof. exact (MK_COMB (@lem1202789 _28101) (@lem1202788 _28101 h t h1)). Qed.
Lemma lem1202795 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term126 _28101 t) = (term152 _28101 t).
Proof. exact (fun_ext (fun h : _28101 => @lem1202790 _28101 h t h1)). Qed.
Lemma lem1202796 {_28101 : Type'} : (@all _28101) = (@all _28101).
Proof. exact (eq_refl (@all _28101)). Qed.
Lemma lem1202797 {_28101 : Type'} (t : list _28101) (h1 : (t = (@nil _28101)) = True) : (term128 _28101 t) = (term153 _28101 t).
Proof. exact (MK_COMB (@lem1202796 _28101) (@lem1202795 _28101 t h1)). Qed.
Lemma lem1202802 {_28101 : Type'} (t : list _28101) : term154 _28101 t.
Proof. exact (fun h0 : (t = (@nil _28101)) = True => @lem1202797 _28101 t h0). Qed.
Lemma lem1202803 {_28101 : Type'} (t : list _28101) : term155 _28101 t.
Proof. exact (conj (@lem1202735 _28101 t) (@lem1202802 _28101 t)). Qed.
Lemma lem1202805 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term91 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1202806 {_28101 : Type'} (t : list _28101) : term156 _28101 t.
Proof. exact (@lem1202805 (term128 _28101 t) (term153 _28101 t) (t = (@nil _28101)) True). Qed.
Lemma lem1202807 {_28101 : Type'} (t : list _28101) : (term128 _28101 t) = (term157 _28101 t).
Proof. exact (@lem1202806 _28101 t (@lem1202803 _28101 t)). Qed.
Lemma lem1202809 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1202810 {_28101 : Type'} (t : list _28101) : (term94 _28101 t) = True.
Proof. exact (@lem1202809 (t = (@nil _28101))). Qed.
Lemma lem1202815 {_28101 : Type'} (t : list _28101) : (term158 _28101 t) = (term158 _28101 t).
Proof. exact (eq_refl (term158 _28101 t)). Qed.
Lemma lem1202816 {_28101 : Type'} (t : list _28101) : (term157 _28101 t) = (term159 _28101 t).
Proof. exact (MK_COMB (@lem1202815 _28101 t) (@lem1202810 _28101 t)). Qed.
Lemma lem1202818 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1202819 {_28101 : Type'} (t : list _28101) : (term159 _28101 t) = (term160 _28101 t).
Proof. exact (@lem1202818 (term160 _28101 t)). Qed.
Lemma lem1202820 {_28101 : Type'} (t : list _28101) : (term157 _28101 t) = (term160 _28101 t).
Proof. exact (TRANS (@lem1202816 _28101 t) (@lem1202819 _28101 t)). Qed.
Lemma lem1202821 {_28101 : Type'} (t : list _28101) : (term128 _28101 t) = (term160 _28101 t).
Proof. exact (TRANS (@lem1202807 _28101 t) (@lem1202820 _28101 t)). Qed.
Lemma lem1202825 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (q = (@nil _28101)) = False.
Proof. exact (h1). Qed.
Lemma lem1202826 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202827 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term67 _28101 q) = (@COND _28101 False).
Proof. exact (MK_COMB (@lem1202826 _28101) (@lem1202825 _28101 q h1)). Qed.
Lemma lem1202828 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202829 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term136 _28101 q h) = (@COND _28101 False h).
Proof. exact (MK_COMB (@lem1202827 _28101 q h1) (@lem1202828 _28101 h)). Qed.
Lemma lem1202831 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (q = (@nil _28101)) = False.
Proof. exact (h1). Qed.
Lemma lem1202832 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202833 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term67 _28101 q) = (@COND _28101 False).
Proof. exact (MK_COMB (@lem1202832 _28101) (@lem1202831 _28101 q h1)). Qed.
Lemma lem1202834 {_28101 : Type'} (t : list _28101) : (@LAST _28101 t) = (@LAST _28101 t).
Proof. exact (eq_refl (@LAST _28101 t)). Qed.
Lemma lem1202835 {_28101 : Type'} (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term138 _28101 q t) = (term161 _28101 t).
Proof. exact (MK_COMB (@lem1202833 _28101 q h1) (@lem1202834 _28101 t)). Qed.
Lemma lem1202836 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202837 {_28101 : Type'} (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term54 _28101 t q) = (term162 _28101 t q).
Proof. exact (MK_COMB (@lem1202835 _28101 t q h1) (@lem1202836 _28101 q)). Qed.
Lemma lem1202839 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1202840 {_28101 : Type'} (t1 : _28101) (t2 : _28101) : (@COND _28101 False t1 t2) = t2.
Proof. exact (@lem1202839 _28101 t1 t2). Qed.
Lemma lem1202841 {_28101 : Type'} (t : list _28101) (q : list _28101) : (term162 _28101 t q) = (@LAST _28101 q).
Proof. exact (@lem1202840 _28101 (@LAST _28101 t) (@LAST _28101 q)). Qed.
Lemma lem1202842 {_28101 : Type'} (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term54 _28101 t q) = (@LAST _28101 q).
Proof. exact (TRANS (@lem1202837 _28101 t q h1) (@lem1202841 _28101 t q)). Qed.
Lemma lem1202843 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term147 _28101 h t q) = (term137 _28101 h q).
Proof. exact (MK_COMB (@lem1202829 _28101 h q h1) (@lem1202842 _28101 t q h1)). Qed.
Lemma lem1202845 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1202846 {_28101 : Type'} (t1 : _28101) (t2 : _28101) : (@COND _28101 False t1 t2) = t2.
Proof. exact (@lem1202845 _28101 t1 t2). Qed.
Lemma lem1202847 {_28101 : Type'} (h : _28101) (q : list _28101) : (term137 _28101 h q) = (@LAST _28101 q).
Proof. exact (@lem1202846 _28101 h (@LAST _28101 q)). Qed.
Lemma lem1202848 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term147 _28101 h t q) = (@LAST _28101 q).
Proof. exact (TRANS (@lem1202843 _28101 t h q h1) (@lem1202847 _28101 h q)). Qed.
Lemma lem1202849 {_28101 : Type'} : (@eq _28101) = (@eq _28101).
Proof. exact (eq_refl (@eq _28101)). Qed.
Lemma lem1202850 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term148 _28101 h t q) = (term35 _28101 q).
Proof. exact (MK_COMB (@lem1202849 _28101) (@lem1202848 _28101 h t q h1)). Qed.
Lemma lem1202852 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (q = (@nil _28101)) = False.
Proof. exact (h1). Qed.
Lemma lem1202853 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202854 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term67 _28101 q) = (@COND _28101 False).
Proof. exact (MK_COMB (@lem1202853 _28101) (@lem1202852 _28101 q h1)). Qed.
Lemma lem1202855 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202856 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term136 _28101 q h) = (@COND _28101 False h).
Proof. exact (MK_COMB (@lem1202854 _28101 q h1) (@lem1202855 _28101 h)). Qed.
Lemma lem1202857 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202858 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term58 _28101 h q) = (term137 _28101 h q).
Proof. exact (MK_COMB (@lem1202856 _28101 h q h1) (@lem1202857 _28101 q)). Qed.
Lemma lem1202860 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1202861 {_28101 : Type'} (t1 : _28101) (t2 : _28101) : (@COND _28101 False t1 t2) = t2.
Proof. exact (@lem1202860 _28101 t1 t2). Qed.
Lemma lem1202862 {_28101 : Type'} (h : _28101) (q : list _28101) : (term137 _28101 h q) = (@LAST _28101 q).
Proof. exact (@lem1202861 _28101 h (@LAST _28101 q)). Qed.
Lemma lem1202863 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : (term58 _28101 h q) = (@LAST _28101 q).
Proof. exact (TRANS (@lem1202858 _28101 h q h1) (@lem1202862 _28101 h q)). Qed.
Lemma lem1202864 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : ((term147 _28101 h t q) = (term58 _28101 h q)) = ((@LAST _28101 q) = (@LAST _28101 q)).
Proof. exact (MK_COMB (@lem1202850 _28101 h t q h1) (@lem1202863 _28101 h q h1)). Qed.
Lemma lem1202866 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1202867 {_28101 : Type'} (x : _28101) : (x = x) = True.
Proof. exact (@lem1202866 _28101 x). Qed.
Lemma lem1202868 {_28101 : Type'} (q : list _28101) : ((@LAST _28101 q) = (@LAST _28101 q)) = True.
Proof. exact (@lem1202867 _28101 (@LAST _28101 q)). Qed.
Lemma lem1202869 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = False) : ((term147 _28101 h t q) = (term58 _28101 h q)) = True.
Proof. exact (TRANS (@lem1202864 _28101 t h q h1) (@lem1202868 _28101 q)). Qed.
Lemma lem1202870 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) : term163 _28101 t h q.
Proof. exact (fun h0 : (q = (@nil _28101)) = False => @lem1202869 _28101 t h q h0). Qed.
Lemma lem1202872 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (q = (@nil _28101)) = True.
Proof. exact (h1). Qed.
Lemma lem1202873 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202874 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term67 _28101 q) = (@COND _28101 True).
Proof. exact (MK_COMB (@lem1202873 _28101) (@lem1202872 _28101 q h1)). Qed.
Lemma lem1202875 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202876 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term136 _28101 q h) = (@COND _28101 True h).
Proof. exact (MK_COMB (@lem1202874 _28101 q h1) (@lem1202875 _28101 h)). Qed.
Lemma lem1202878 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (q = (@nil _28101)) = True.
Proof. exact (h1). Qed.
Lemma lem1202879 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202880 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term67 _28101 q) = (@COND _28101 True).
Proof. exact (MK_COMB (@lem1202879 _28101) (@lem1202878 _28101 q h1)). Qed.
Lemma lem1202881 {_28101 : Type'} (t : list _28101) : (@LAST _28101 t) = (@LAST _28101 t).
Proof. exact (eq_refl (@LAST _28101 t)). Qed.
Lemma lem1202882 {_28101 : Type'} (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term138 _28101 q t) = (term164 _28101 t).
Proof. exact (MK_COMB (@lem1202880 _28101 q h1) (@lem1202881 _28101 t)). Qed.
Lemma lem1202883 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202884 {_28101 : Type'} (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term54 _28101 t q) = (term165 _28101 t q).
Proof. exact (MK_COMB (@lem1202882 _28101 t q h1) (@lem1202883 _28101 q)). Qed.
Lemma lem1202886 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1202887 {_28101 : Type'} (t2 : _28101) (t1 : _28101) : (@COND _28101 True t1 t2) = t1.
Proof. exact (@lem1202886 _28101 t2 t1). Qed.
Lemma lem1202888 {_28101 : Type'} (q : list _28101) (t : list _28101) : (term165 _28101 t q) = (@LAST _28101 t).
Proof. exact (@lem1202887 _28101 (@LAST _28101 q) (@LAST _28101 t)). Qed.
Lemma lem1202889 {_28101 : Type'} (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term54 _28101 t q) = (@LAST _28101 t).
Proof. exact (TRANS (@lem1202884 _28101 t q h1) (@lem1202888 _28101 q t)). Qed.
Lemma lem1202890 {_28101 : Type'} (h : _28101) (t : list _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term147 _28101 h t q) = (term149 _28101 h t).
Proof. exact (MK_COMB (@lem1202876 _28101 h q h1) (@lem1202889 _28101 t q h1)). Qed.
Lemma lem1202892 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1202893 {_28101 : Type'} (t2 : _28101) (t1 : _28101) : (@COND _28101 True t1 t2) = t1.
Proof. exact (@lem1202892 _28101 t2 t1). Qed.
Lemma lem1202894 {_28101 : Type'} (t : list _28101) (h : _28101) : (term149 _28101 h t) = h.
Proof. exact (@lem1202893 _28101 (@LAST _28101 t) h). Qed.
Lemma lem1202895 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term147 _28101 h t q) = h.
Proof. exact (TRANS (@lem1202890 _28101 h t q h1) (@lem1202894 _28101 t h)). Qed.
Lemma lem1202896 {_28101 : Type'} : (@eq _28101) = (@eq _28101).
Proof. exact (eq_refl (@eq _28101)). Qed.
Lemma lem1202897 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term148 _28101 h t q) = (@eq _28101 h).
Proof. exact (MK_COMB (@lem1202896 _28101) (@lem1202895 _28101 t h q h1)). Qed.
Lemma lem1202899 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (q = (@nil _28101)) = True.
Proof. exact (h1). Qed.
Lemma lem1202900 {_28101 : Type'} : (@COND _28101) = (@COND _28101).
Proof. exact (eq_refl (@COND _28101)). Qed.
Lemma lem1202901 {_28101 : Type'} (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term67 _28101 q) = (@COND _28101 True).
Proof. exact (MK_COMB (@lem1202900 _28101) (@lem1202899 _28101 q h1)). Qed.
Lemma lem1202902 {_28101 : Type'} (h : _28101) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1202903 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term136 _28101 q h) = (@COND _28101 True h).
Proof. exact (MK_COMB (@lem1202901 _28101 q h1) (@lem1202902 _28101 h)). Qed.
Lemma lem1202904 {_28101 : Type'} (q : list _28101) : (@LAST _28101 q) = (@LAST _28101 q).
Proof. exact (eq_refl (@LAST _28101 q)). Qed.
Lemma lem1202905 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term58 _28101 h q) = (term149 _28101 h q).
Proof. exact (MK_COMB (@lem1202903 _28101 h q h1) (@lem1202904 _28101 q)). Qed.
Lemma lem1202907 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1202908 {_28101 : Type'} (t2 : _28101) (t1 : _28101) : (@COND _28101 True t1 t2) = t1.
Proof. exact (@lem1202907 _28101 t2 t1). Qed.
Lemma lem1202909 {_28101 : Type'} (q : list _28101) (h : _28101) : (term149 _28101 h q) = h.
Proof. exact (@lem1202908 _28101 (@LAST _28101 q) h). Qed.
Lemma lem1202910 {_28101 : Type'} (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : (term58 _28101 h q) = h.
Proof. exact (TRANS (@lem1202905 _28101 h q h1) (@lem1202909 _28101 q h)). Qed.
Lemma lem1202911 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : ((term147 _28101 h t q) = (term58 _28101 h q)) = (h = h).
Proof. exact (MK_COMB (@lem1202897 _28101 t h q h1) (@lem1202910 _28101 h q h1)). Qed.
Lemma lem1202913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1202914 {_28101 : Type'} (x : _28101) : (x = x) = True.
Proof. exact (@lem1202913 _28101 x). Qed.
Lemma lem1202915 {_28101 : Type'} (h : _28101) : (h = h) = True.
Proof. exact (@lem1202914 _28101 h). Qed.
Lemma lem1202916 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) (h1 : (q = (@nil _28101)) = True) : ((term147 _28101 h t q) = (term58 _28101 h q)) = True.
Proof. exact (TRANS (@lem1202911 _28101 t h q h1) (@lem1202915 _28101 h)). Qed.
Lemma lem1202917 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) : term166 _28101 t h q.
Proof. exact (fun h0 : (q = (@nil _28101)) = True => @lem1202916 _28101 t h q h0). Qed.
Lemma lem1202918 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) : term167 _28101 t h q.
Proof. exact (conj (@lem1202870 _28101 t h q) (@lem1202917 _28101 t h q)). Qed.
Lemma lem1202920 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term91 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem1202921 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) : term168 _28101 t h q.
Proof. exact (@lem1202920 ((term147 _28101 h t q) = (term58 _28101 h q)) True (q = (@nil _28101)) True). Qed.
Lemma lem1202922 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) : ((term147 _28101 h t q) = (term58 _28101 h q)) = (term169 _28101 q).
Proof. exact (@lem1202921 _28101 t h q (@lem1202918 _28101 t h q)). Qed.
Lemma lem1202924 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1202925 {_28101 : Type'} (q : list _28101) : (term94 _28101 q) = True.
Proof. exact (@lem1202924 (q = (@nil _28101))). Qed.
Lemma lem1202927 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1202928 {_28101 : Type'} (q : list _28101) : (term170 _28101 q) = True.
Proof. exact (@lem1202927 (term108 _28101 q)). Qed.
Lemma lem1202929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1202930 {_28101 : Type'} (q : list _28101) : (term171 _28101 q) = (and True).
Proof. exact (MK_COMB (@lem1202929) (@lem1202928 _28101 q)). Qed.
Lemma lem1202931 {_28101 : Type'} (q : list _28101) : (term169 _28101 q) = (True /\ True).
Proof. exact (MK_COMB (@lem1202930 _28101 q) (@lem1202925 _28101 q)). Qed.
Lemma lem1202933 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1202934 : (True /\ True) = True.
Proof. exact (@lem1202933 True). Qed.
Lemma lem1202935 {_28101 : Type'} (q : list _28101) : (term169 _28101 q) = True.
Proof. exact (TRANS (@lem1202931 _28101 q) (@lem1202934)). Qed.
Lemma lem1202940 {_28101 : Type'} (t : list _28101) (h : _28101) (q : list _28101) : ((term147 _28101 h t q) = (term58 _28101 h q)) = True.
Proof. exact (TRANS (@lem1202922 _28101 t h q) (@lem1202935 _28101 q)). Qed.
Lemma lem1202941 {_28101 : Type'} (t : list _28101) (h : _28101) : (term150 _28101 t h) = (term139 _28101).
Proof. exact (fun_ext (fun q : list _28101 => @lem1202940 _28101 t h q)). Qed.
Lemma lem1202942 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202943 {_28101 : Type'} (t : list _28101) (h : _28101) : (term151 _28101 t h) = (term140 _28101).
Proof. exact (MK_COMB (@lem1202942 _28101) (@lem1202941 _28101 t h)). Qed.
Lemma lem1202944 {_28101 : Type'} (t : list _28101) : (term152 _28101 t) = (term172 _28101).
Proof. exact (fun_ext (fun h : _28101 => @lem1202943 _28101 t h)). Qed.
Lemma lem1202945 {_28101 : Type'} : (@all _28101) = (@all _28101).
Proof. exact (eq_refl (@all _28101)). Qed.
Lemma lem1202946 {_28101 : Type'} (t : list _28101) : (term153 _28101 t) = (term173 _28101).
Proof. exact (MK_COMB (@lem1202945 _28101) (@lem1202944 _28101 t)). Qed.
Lemma lem1202951 {_28101 : Type'} (t : list _28101) : (term174 _28101 t) = (term174 _28101 t).
Proof. exact (eq_refl (term174 _28101 t)). Qed.
Lemma lem1202952 {_28101 : Type'} (t : list _28101) : (term160 _28101 t) = (term175 _28101 t).
Proof. exact (MK_COMB (@lem1202951 _28101 t) (@lem1202946 _28101 t)). Qed.
Lemma lem1202953 {_28101 : Type'} (t : list _28101) : (term176 _28101 t) = (term176 _28101 t).
Proof. exact (eq_refl (term176 _28101 t)). Qed.
Lemma lem1202954 {_28101 : Type'} (t : list _28101) : ((term128 _28101 t) = (term160 _28101 t)) = ((term128 _28101 t) = (term175 _28101 t)).
Proof. exact (MK_COMB (@lem1202953 _28101 t) (@lem1202952 _28101 t)). Qed.
Lemma lem1202955 {_28101 : Type'} (t : list _28101) : (term128 _28101 t) = (term175 _28101 t).
Proof. exact (EQ_MP (@lem1202954 _28101 t) (@lem1202821 _28101 t)). Qed.
Lemma lem1202956 {_28101 : Type'} : (term130 _28101) = (term177 _28101).
Proof. exact (fun_ext (fun t : list _28101 => @lem1202955 _28101 t)). Qed.
Lemma lem1202957 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202958 {_28101 : Type'} : (term132 _28101) = (term178 _28101).
Proof. exact (MK_COMB (@lem1202957 _28101) (@lem1202956 _28101)). Qed.
Lemma lem1202959 {_28101 : Type'} : (term131 _28101) = (term178 _28101).
Proof. exact (TRANS (@lem1202658 _28101) (@lem1202958 _28101)). Qed.
Lemma lem1202969 {A : Type'} (t : Prop) : (term141 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem1202970 {_28101 : Type'} (t : Prop) : (term141 _28101 t) = t.
Proof. exact (@lem1202969 _28101 t). Qed.
Lemma lem1202971 {_28101 : Type'} : (term173 _28101) = (term140 _28101).
Proof. exact (@lem1202970 _28101 (term140 _28101)). Qed.
Lemma lem1202973 {A : Type'} (t : Prop) : (term141 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem1202974 {_28101 : Type'} (t : Prop) : (term142 _28101 t) = t.
Proof. exact (@lem1202973 (list _28101) t). Qed.
Lemma lem1202975 {_28101 : Type'} : (term140 _28101) = True.
Proof. exact (@lem1202974 _28101 True). Qed.
Lemma lem1202976 {_28101 : Type'} : (term173 _28101) = True.
Proof. exact (TRANS (@lem1202971 _28101) (@lem1202975 _28101)). Qed.
Lemma lem1202977 {_28101 : Type'} (t : list _28101) : (term174 _28101 t) = (term174 _28101 t).
Proof. exact (eq_refl (term174 _28101 t)). Qed.
Lemma lem1202978 {_28101 : Type'} (t : list _28101) : (term175 _28101 t) = (term170 _28101 t).
Proof. exact (MK_COMB (@lem1202977 _28101 t) (@lem1202976 _28101)). Qed.
Lemma lem1202980 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem21750 t)). Qed.
Lemma lem1202981 {_28101 : Type'} (t : list _28101) : (term170 _28101 t) = True.
Proof. exact (@lem1202980 (term108 _28101 t)). Qed.
Lemma lem1202982 {_28101 : Type'} (t : list _28101) : (term175 _28101 t) = True.
Proof. exact (TRANS (@lem1202978 _28101 t) (@lem1202981 _28101 t)). Qed.
Lemma lem1202983 {_28101 : Type'} : (term177 _28101) = (term139 _28101).
Proof. exact (fun_ext (fun t : list _28101 => @lem1202982 _28101 t)). Qed.
Lemma lem1202984 {_28101 : Type'} : (@all (list _28101)) = (@all (list _28101)).
Proof. exact (eq_refl (@all (list _28101))). Qed.
Lemma lem1202985 {_28101 : Type'} : (term178 _28101) = (term140 _28101).
Proof. exact (MK_COMB (@lem1202984 _28101) (@lem1202983 _28101)). Qed.
Lemma lem1202987 {A : Type'} (t : Prop) : (term141 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem1202988 {_28101 : Type'} (t : Prop) : (term142 _28101 t) = t.
Proof. exact (@lem1202987 (list _28101) t). Qed.
Lemma lem1202989 {_28101 : Type'} : (term140 _28101) = True.
Proof. exact (@lem1202988 _28101 True). Qed.
Lemma lem1202990 {_28101 : Type'} : (term178 _28101) = True.
Proof. exact (TRANS (@lem1202985 _28101) (@lem1202989 _28101)). Qed.
Lemma lem1202991 {_28101 : Type'} : (term131 _28101) = True.
Proof. exact (TRANS (@lem1202959 _28101) (@lem1202990 _28101)). Qed.
Lemma lem1202992 {_28101 : Type'} : True = (term131 _28101).
Proof. exact (SYM (@lem1202991 _28101)). Qed.
Lemma lem1202993 {_28101 : Type'} : term131 _28101.
Proof. exact (EQ_MP (@lem1202992 _28101) (@lem0)). Qed.
Lemma lem1202994 {_28101 : Type'} (t : list _28101) : term179 _28101 t.
Proof. exact (@lem1202993 _28101 t). Qed.
Lemma lem1202995 {_28101 : Type'} (t : list _28101) : (term179 _28101 t) = (term127 _28101 t).
Proof. exact (eq_refl (term179 _28101 t)). Qed.
Lemma lem1202996 {_28101 : Type'} (t : list _28101) : term127 _28101 t.
Proof. exact (EQ_MP (@lem1202995 _28101 t) (@lem1202994 _28101 t)). Qed.
Lemma lem1202997 {_28101 : Type'} (t : list _28101) (h : _28101) : term180 _28101 t h.
Proof. exact (@lem1202996 _28101 t h). Qed.
Lemma lem1202998 {_28101 : Type'} (h : _28101) (t : list _28101) : (term180 _28101 t h) = (term119 _28101 h t).
Proof. exact (eq_refl (term180 _28101 t h)). Qed.
Lemma lem1202999 {_28101 : Type'} (h : _28101) (t : list _28101) : term119 _28101 h t.
Proof. exact (EQ_MP (@lem1202998 _28101 h t) (@lem1202997 _28101 t h)). Qed.
Lemma lem1203001 {_28101 : Type'} (h : _28101) (t : list _28101) : term119 _28101 h t.
Proof. exact (@lem1202619 _28101 h t (@lem1202999 _28101 h t)). Qed.
Lemma lem1203002 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term120 _28101 h t) : False.
Proof. exact (@lem1203001 _28101 h t (@lem1202603 _28101 h t h1)). Qed.
Lemma lem1203003 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term120 _28101 h t) : (term120 _28101 h t) = False.
Proof. exact (prop_ext (fun h2 : term120 _28101 h t => @lem1203002 _28101 h t h1) (fun h2 : False => @lem1202603 _28101 h t h1)). Qed.
Lemma lem1203004 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term120 _28101 h t) : False.
Proof. exact (EQ_MP (@lem1203003 _28101 h t h1) (@lem1202603 _28101 h t h1)). Qed.
Lemma lem1203005 {_28101 : Type'} (h : _28101) (t : list _28101) : term119 _28101 h t.
Proof. exact (fun h0 : term120 _28101 h t => @lem1203004 _28101 h t h0). Qed.
Lemma lem1203006 {_28101 : Type'} (h : _28101) (t : list _28101) : term74 _28101 h t.
Proof. exact (EQ_MP (@lem1202602 _28101 h t) (@lem1203005 _28101 h t)). Qed.
Lemma lem1203007 {_28101 : Type'} (h : _28101) (t : list _28101) (h1 : term8 _28101 t) : term12 _28101 h t.
Proof. exact (EQ_MP (@lem1202342 _28101 h t h1) (@lem1203006 _28101 h t)). Qed.
Lemma lem1203008 {_28101 : Type'} : term4 _28101.
Proof. exact (EQ_MP (@lem1202247 _28101) (@lem1202598 _28101)). Qed.
Lemma lem1203009 {_28101 : Type'} (h : _28101) (t : list _28101) : term14 _28101 h t.
Proof. exact (fun h0 : term8 _28101 t => @lem1203007 _28101 h t h0). Qed.
Lemma lem1203014 {_28101 : Type'} (h : _28101) : term18 _28101 h.
Proof. exact (fun t : list _28101 => @lem1203009 _28101 h t). Qed.
Lemma lem1203019 {_28101 : Type'} : term22 _28101.
Proof. exact (fun h : _28101 => @lem1203014 _28101 h). Qed.
Lemma lem1203020 {_28101 : Type'} : term24 _28101.
Proof. exact (conj (@lem1203008 _28101) (@lem1203019 _28101)). Qed.
Lemma lem1203021 {_28101 : Type'} : term29 _28101.
Proof. exact (@lem1202196 _28101 (@lem1203020 _28101)). Qed.
