Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_CART_UNIV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_CART_UNIV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
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
Lemma lem7990979 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7990980 {A N : Type'} : (term1 A N) = (term2 A N).
Proof. exact (@lem7990979 (term1 A N)). Qed.
Lemma lem7990981 {A N : Type'} : (term2 A N) = (term1 A N).
Proof. exact (SYM (@lem7990980 A N)). Qed.
Lemma lem7990982 {A N : Type'} (h1 : term3 A N) : term3 A N.
Proof. exact (h1). Qed.
Lemma lem7990983 {A N : Type'} : term4 A N.
Proof. exact (@lem7990967 A N). Qed.
Lemma lem7990984 {A N : Type'} : term5 A N.
Proof. exact (@lem7990967 (cart A N) N). Qed.
Lemma lem7990985 {N : Type'} : term6 N.
Proof. exact (@lem7990967 N N). Qed.
Lemma lem7990988 {A : Type'} : term6 A.
Proof. exact (@lem7990967 A A). Qed.
Lemma lem7990989 {A N : Type'} : term7 A N.
Proof. exact (@lem7990967 A (cart A N)). Qed.
Lemma lem7990991 {A N : Type'} : term8 A N.
Proof. exact (@lem3863773 (cart A N)). Qed.
Lemma lem7990992 {A N : Type'} : term9 A N.
Proof. exact (@lem3863773 (type0 A N)). Qed.
Lemma lem7990993 {N : Type'} : term10 N.
Proof. exact (@lem3863773 N). Qed.
Lemma lem7990994 {N : Type'} : term11 N.
Proof. exact (@lem3863773 (cart N N)). Qed.
Lemma lem7990995 {A : Type'} : term10 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem7990996 {A N : Type'} : term12 A N.
Proof. exact (@lem3863773 (type1 A N)). Qed.
Lemma lem7990997 {A : Type'} : term11 A.
Proof. exact (@lem3863773 (cart A A)). Qed.
Lemma lem7991003 {_100044 A N : Type'} (h1 : term13 _100044 A N) : term13 _100044 A N.
Proof. exact (h1). Qed.
Lemma lem7991004 {_100044 A N : Type'} : term14 _100044 A N.
Proof. exact (fun h0 : term13 _100044 A N => @lem7991003 _100044 A N h0). Qed.
Lemma lem7991005 {_100044 A N : Type'} (h1 : term14 _100044 A N) : term14 _100044 A N.
Proof. exact (h1). Qed.
Lemma lem7991006 {_100044 A N : Type'} (h1 : term13 _100044 A N) : term13 _100044 A N.
Proof. exact (h1). Qed.
Lemma lem7991007 {_100044 A N : Type'} (h1 : term13 _100044 A N) (h2 : term14 _100044 A N) : term13 _100044 A N.
Proof. exact (@lem7991005 _100044 A N h2 (@lem7991006 _100044 A N h1)). Qed.
Lemma lem7991008 {_100044 A N : Type'} (h1 : term13 _100044 A N) : term15 _100044 A N.
Proof. exact (fun h0 : term14 _100044 A N => @lem7991007 _100044 A N h1 h0). Qed.
Lemma lem7991009 {_100044 A N : Type'} (h1 : term14 _100044 A N) : term14 _100044 A N.
Proof. exact (h1). Qed.
Lemma lem7991010 {_100044 A N : Type'} (h1 : term13 _100044 A N) (h2 : term14 _100044 A N) : term13 _100044 A N.
Proof. exact (@lem7991008 _100044 A N h1 (@lem7991009 _100044 A N h2)). Qed.
Lemma lem7991011 {_100044 A N : Type'} (h1 : term14 _100044 A N) : term14 _100044 A N.
Proof. exact (fun h0 : term13 _100044 A N => @lem7991010 _100044 A N h0 h1). Qed.
Lemma lem7991012 {_100044 A N : Type'} : term16 _100044 A N.
Proof. exact (fun h0 : term14 _100044 A N => @lem7991011 _100044 A N h0). Qed.
Lemma lem7991015 {_100044 A N : Type'} : term14 _100044 A N.
Proof. exact (@lem7991012 _100044 A N (@lem7991004 _100044 A N)). Qed.
Lemma lem7991016 {_100044 A N : Type'} : term14 _100044 A N.
Proof. exact (@lem7991015 _100044 A N). Qed.
Lemma lem7991150 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7991151 {A N : Type'} : (term17 A N) = (term18 A N).
Proof. exact (@lem7991150 (term5 A N)). Qed.
Lemma lem7991158 {N : Type'} : (term19 N) = (term19 N).
Proof. exact (eq_refl (term19 N)). Qed.
Lemma lem7991159 {A N : Type'} : (term20 A N) = (term21 A N).
Proof. exact (MK_COMB (@lem7991158 N) (@lem7991151 A N)). Qed.
Lemma lem7991162 {A N : Type'} : (term22 A N) = (term22 A N).
Proof. exact (eq_refl (term22 A N)). Qed.
Lemma lem7991163 {A N : Type'} : (term23 A N) = (term24 A N).
Proof. exact (MK_COMB (@lem7991162 A N) (@lem7991159 A N)). Qed.
Lemma lem7991166 {A N : Type'} : (term25 A N) = (term25 A N).
Proof. exact (eq_refl (term25 A N)). Qed.
Lemma lem7991167 {A N : Type'} : (term26 A N) = (term27 A N).
Proof. exact (MK_COMB (@lem7991166 A N) (@lem7991163 A N)). Qed.
Lemma lem7991170 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7991171 {A N : Type'} : (term28 A N) = (term29 A N).
Proof. exact (MK_COMB (@lem7991170 A) (@lem7991167 A N)). Qed.
Lemma lem7991174 {A N : Type'} : (term30 A N) = (term30 A N).
Proof. exact (eq_refl (term30 A N)). Qed.
Lemma lem7991175 {A N : Type'} : (term31 A N) = (term32 A N).
Proof. exact (MK_COMB (@lem7991174 A N) (@lem7991171 A N)). Qed.
Lemma lem7991178 {N : Type'} : (term33 N) = (term33 N).
Proof. exact (eq_refl (term33 N)). Qed.
Lemma lem7991179 {A N : Type'} : (term34 A N) = (term35 A N).
Proof. exact (MK_COMB (@lem7991178 N) (@lem7991175 A N)). Qed.
Lemma lem7991182 {A N : Type'} : (term36 A N) = (term36 A N).
Proof. exact (eq_refl (term36 A N)). Qed.
Lemma lem7991183 {A N : Type'} : (term37 A N) = (term38 A N).
Proof. exact (MK_COMB (@lem7991182 A N) (@lem7991179 A N)). Qed.
Lemma lem7991186 {A N : Type'} : (term39 A N) = (term39 A N).
Proof. exact (eq_refl (term39 A N)). Qed.
Lemma lem7991187 {A N : Type'} : (term40 A N) = (term41 A N).
Proof. exact (MK_COMB (@lem7991186 A N) (@lem7991183 A N)). Qed.
Lemma lem7991190 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (eq_refl (term33 A)). Qed.
Lemma lem7991191 {A N : Type'} : (term42 A N) = (term43 A N).
Proof. exact (MK_COMB (@lem7991190 A) (@lem7991187 A N)). Qed.
Lemma lem7991194 {N : Type'} : (term44 N) = (term44 N).
Proof. exact (eq_refl (term44 N)). Qed.
Lemma lem7991195 {A N : Type'} : (term45 A N) = (term46 A N).
Proof. exact (MK_COMB (@lem7991194 N) (@lem7991191 A N)). Qed.
Lemma lem7991198 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (eq_refl (term44 A)). Qed.
Lemma lem7991199 {A N : Type'} : (term47 A N) = (term48 A N).
Proof. exact (MK_COMB (@lem7991198 A) (@lem7991195 A N)). Qed.
Lemma lem7991202 {_100044 : Type'} : (term44 _100044) = (term44 _100044).
Proof. exact (eq_refl (term44 _100044)). Qed.
Lemma lem7991203 {_100044 A N : Type'} : (term49 _100044 A N) = (term50 _100044 A N).
Proof. exact (MK_COMB (@lem7991202 _100044) (@lem7991199 A N)). Qed.
Lemma lem7991206 {A N : Type'} : (term51 A N) = (term51 A N).
Proof. exact (eq_refl (term51 A N)). Qed.
Lemma lem7991213 {_100044 A N : Type'} : (term13 _100044 A N) = (term52 _100044 A N).
Proof. exact (MK_COMB (@lem7991206 A N) (@lem7991203 _100044 A N)). Qed.
Lemma lem7991218 {A N : Type'} (m : nat) : (term53 A N m) = (term53 A N m).
Proof. exact (eq_refl (term53 A N m)). Qed.
Lemma lem7991219 {A N : Type'} : (term54 A N) = (term54 A N).
Proof. exact (fun_ext (fun m : nat => @lem7991218 A N m)). Qed.
Lemma lem7991220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991221 {A N : Type'} : (term5 A N) = (term5 A N).
Proof. exact (MK_COMB (@lem7991220) (@lem7991219 A N)). Qed.
Lemma lem7991222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7991223 {A N : Type'} : (term18 A N) = (term18 A N).
Proof. exact (MK_COMB (@lem7991222) (@lem7991221 A N)). Qed.
Lemma lem7991228 {N : Type'} (m : nat) : (term55 N m) = (term55 N m).
Proof. exact (eq_refl (term55 N m)). Qed.
Lemma lem7991229 {N : Type'} : (term56 N) = (term56 N).
Proof. exact (fun_ext (fun m : nat => @lem7991228 N m)). Qed.
Lemma lem7991230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991231 {N : Type'} : (term6 N) = (term6 N).
Proof. exact (MK_COMB (@lem7991230) (@lem7991229 N)). Qed.
Lemma lem7991232 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991233 {N : Type'} : (term19 N) = (term19 N).
Proof. exact (MK_COMB (@lem7991232) (@lem7991231 N)). Qed.
Lemma lem7991234 {A N : Type'} : (term21 A N) = (term21 A N).
Proof. exact (MK_COMB (@lem7991233 N) (@lem7991223 A N)). Qed.
Lemma lem7991239 {A N : Type'} (m : nat) : (term57 A N m) = (term57 A N m).
Proof. exact (eq_refl (term57 A N m)). Qed.
Lemma lem7991240 {A N : Type'} : (term58 A N) = (term58 A N).
Proof. exact (fun_ext (fun m : nat => @lem7991239 A N m)). Qed.
Lemma lem7991241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991242 {A N : Type'} : (term7 A N) = (term7 A N).
Proof. exact (MK_COMB (@lem7991241) (@lem7991240 A N)). Qed.
Lemma lem7991243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991244 {A N : Type'} : (term22 A N) = (term22 A N).
Proof. exact (MK_COMB (@lem7991243) (@lem7991242 A N)). Qed.
Lemma lem7991245 {A N : Type'} : (term24 A N) = (term24 A N).
Proof. exact (MK_COMB (@lem7991244 A N) (@lem7991234 A N)). Qed.
Lemma lem7991250 {A N : Type'} (m : nat) : (term59 A N m) = (term59 A N m).
Proof. exact (eq_refl (term59 A N m)). Qed.
Lemma lem7991251 {A N : Type'} : (term60 A N) = (term60 A N).
Proof. exact (fun_ext (fun m : nat => @lem7991250 A N m)). Qed.
Lemma lem7991252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991253 {A N : Type'} : (term4 A N) = (term4 A N).
Proof. exact (MK_COMB (@lem7991252) (@lem7991251 A N)). Qed.
Lemma lem7991254 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991255 {A N : Type'} : (term25 A N) = (term25 A N).
Proof. exact (MK_COMB (@lem7991254) (@lem7991253 A N)). Qed.
Lemma lem7991256 {A N : Type'} : (term27 A N) = (term27 A N).
Proof. exact (MK_COMB (@lem7991255 A N) (@lem7991245 A N)). Qed.
Lemma lem7991261 {A : Type'} (m : nat) : (term55 A m) = (term55 A m).
Proof. exact (eq_refl (term55 A m)). Qed.
Lemma lem7991262 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (fun_ext (fun m : nat => @lem7991261 A m)). Qed.
Lemma lem7991263 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991264 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem7991263) (@lem7991262 A)). Qed.
Lemma lem7991265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991266 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7991265) (@lem7991264 A)). Qed.
Lemma lem7991267 {A N : Type'} : (term29 A N) = (term29 A N).
Proof. exact (MK_COMB (@lem7991266 A) (@lem7991256 A N)). Qed.
Lemma lem7991276 {A N : Type'} (s : type11 A N) (n : nat) : ((@HAS_SIZE (cart (cart A N) N) s n) = (term61 A N s n)) = ((@HAS_SIZE (cart (cart A N) N) s n) = (term61 A N s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart (cart A N) N) s n) = (term61 A N s n))). Qed.
Lemma lem7991277 {A N : Type'} (s : type11 A N) : (term62 A N s) = (term62 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7991276 A N s n)). Qed.
Lemma lem7991278 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991279 {A N : Type'} (s : type11 A N) : (term63 A N s) = (term63 A N s).
Proof. exact (MK_COMB (@lem7991278) (@lem7991277 A N s)). Qed.
Lemma lem7991280 {A N : Type'} : (term64 A N) = (term64 A N).
Proof. exact (fun_ext (fun s : type11 A N => @lem7991279 A N s)). Qed.
Lemma lem7991281 {A N : Type'} : (@all ((cart (cart A N) N) -> Prop)) = (@all ((cart (cart A N) N) -> Prop)).
Proof. exact (eq_refl (@all ((cart (cart A N) N) -> Prop))). Qed.
Lemma lem7991282 {A N : Type'} : (term9 A N) = (term9 A N).
Proof. exact (MK_COMB (@lem7991281 A N) (@lem7991280 A N)). Qed.
Lemma lem7991283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991284 {A N : Type'} : (term30 A N) = (term30 A N).
Proof. exact (MK_COMB (@lem7991283) (@lem7991282 A N)). Qed.
Lemma lem7991285 {A N : Type'} : (term32 A N) = (term32 A N).
Proof. exact (MK_COMB (@lem7991284 A N) (@lem7991267 A N)). Qed.
Lemma lem7991294 {N : Type'} (s : type17 N) (n : nat) : ((@HAS_SIZE (cart N N) s n) = (term65 N s n)) = ((@HAS_SIZE (cart N N) s n) = (term65 N s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart N N) s n) = (term65 N s n))). Qed.
Lemma lem7991295 {N : Type'} (s : type17 N) : (term66 N s) = (term66 N s).
Proof. exact (fun_ext (fun n : nat => @lem7991294 N s n)). Qed.
Lemma lem7991296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991297 {N : Type'} (s : type17 N) : (term67 N s) = (term67 N s).
Proof. exact (MK_COMB (@lem7991296) (@lem7991295 N s)). Qed.
Lemma lem7991298 {N : Type'} : (term68 N) = (term68 N).
Proof. exact (fun_ext (fun s : type17 N => @lem7991297 N s)). Qed.
Lemma lem7991299 {N : Type'} : (@all ((cart N N) -> Prop)) = (@all ((cart N N) -> Prop)).
Proof. exact (eq_refl (@all ((cart N N) -> Prop))). Qed.
Lemma lem7991300 {N : Type'} : (term11 N) = (term11 N).
Proof. exact (MK_COMB (@lem7991299 N) (@lem7991298 N)). Qed.
Lemma lem7991301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991302 {N : Type'} : (term33 N) = (term33 N).
Proof. exact (MK_COMB (@lem7991301) (@lem7991300 N)). Qed.
Lemma lem7991303 {A N : Type'} : (term35 A N) = (term35 A N).
Proof. exact (MK_COMB (@lem7991302 N) (@lem7991285 A N)). Qed.
Lemma lem7991312 {A N : Type'} (s : type12 A N) (n : nat) : ((@HAS_SIZE (cart A (cart A N)) s n) = (term69 A N s n)) = ((@HAS_SIZE (cart A (cart A N)) s n) = (term69 A N s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart A (cart A N)) s n) = (term69 A N s n))). Qed.
Lemma lem7991313 {A N : Type'} (s : type12 A N) : (term70 A N s) = (term70 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7991312 A N s n)). Qed.
Lemma lem7991314 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991315 {A N : Type'} (s : type12 A N) : (term71 A N s) = (term71 A N s).
Proof. exact (MK_COMB (@lem7991314) (@lem7991313 A N s)). Qed.
Lemma lem7991316 {A N : Type'} : (term72 A N) = (term72 A N).
Proof. exact (fun_ext (fun s : type12 A N => @lem7991315 A N s)). Qed.
Lemma lem7991317 {A N : Type'} : (@all ((cart A (cart A N)) -> Prop)) = (@all ((cart A (cart A N)) -> Prop)).
Proof. exact (eq_refl (@all ((cart A (cart A N)) -> Prop))). Qed.
Lemma lem7991318 {A N : Type'} : (term12 A N) = (term12 A N).
Proof. exact (MK_COMB (@lem7991317 A N) (@lem7991316 A N)). Qed.
Lemma lem7991319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991320 {A N : Type'} : (term36 A N) = (term36 A N).
Proof. exact (MK_COMB (@lem7991319) (@lem7991318 A N)). Qed.
Lemma lem7991321 {A N : Type'} : (term38 A N) = (term38 A N).
Proof. exact (MK_COMB (@lem7991320 A N) (@lem7991303 A N)). Qed.
Lemma lem7991330 {A N : Type'} (s : type24 A N) (n : nat) : ((@HAS_SIZE (cart A N) s n) = (term73 A N s n)) = ((@HAS_SIZE (cart A N) s n) = (term73 A N s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart A N) s n) = (term73 A N s n))). Qed.
Lemma lem7991331 {A N : Type'} (s : type24 A N) : (term74 A N s) = (term74 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7991330 A N s n)). Qed.
Lemma lem7991332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991333 {A N : Type'} (s : type24 A N) : (term75 A N s) = (term75 A N s).
Proof. exact (MK_COMB (@lem7991332) (@lem7991331 A N s)). Qed.
Lemma lem7991334 {A N : Type'} : (term76 A N) = (term76 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7991333 A N s)). Qed.
Lemma lem7991335 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7991336 {A N : Type'} : (term8 A N) = (term8 A N).
Proof. exact (MK_COMB (@lem7991335 A N) (@lem7991334 A N)). Qed.
Lemma lem7991337 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991338 {A N : Type'} : (term39 A N) = (term39 A N).
Proof. exact (MK_COMB (@lem7991337) (@lem7991336 A N)). Qed.
Lemma lem7991339 {A N : Type'} : (term41 A N) = (term41 A N).
Proof. exact (MK_COMB (@lem7991338 A N) (@lem7991321 A N)). Qed.
Lemma lem7991348 {A : Type'} (s : type17 A) (n : nat) : ((@HAS_SIZE (cart A A) s n) = (term65 A s n)) = ((@HAS_SIZE (cart A A) s n) = (term65 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (cart A A) s n) = (term65 A s n))). Qed.
Lemma lem7991349 {A : Type'} (s : type17 A) : (term66 A s) = (term66 A s).
Proof. exact (fun_ext (fun n : nat => @lem7991348 A s n)). Qed.
Lemma lem7991350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991351 {A : Type'} (s : type17 A) : (term67 A s) = (term67 A s).
Proof. exact (MK_COMB (@lem7991350) (@lem7991349 A s)). Qed.
Lemma lem7991352 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (fun_ext (fun s : type17 A => @lem7991351 A s)). Qed.
Lemma lem7991353 {A : Type'} : (@all ((cart A A) -> Prop)) = (@all ((cart A A) -> Prop)).
Proof. exact (eq_refl (@all ((cart A A) -> Prop))). Qed.
Lemma lem7991354 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7991353 A) (@lem7991352 A)). Qed.
Lemma lem7991355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991356 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem7991355) (@lem7991354 A)). Qed.
Lemma lem7991357 {A N : Type'} : (term43 A N) = (term43 A N).
Proof. exact (MK_COMB (@lem7991356 A) (@lem7991339 A N)). Qed.
Lemma lem7991366 {N : Type'} (s : N -> Prop) (n : nat) : ((@HAS_SIZE N s n) = (term77 N s n)) = ((@HAS_SIZE N s n) = (term77 N s n)).
Proof. exact (eq_refl ((@HAS_SIZE N s n) = (term77 N s n))). Qed.
Lemma lem7991367 {N : Type'} (s : N -> Prop) : (term78 N s) = (term78 N s).
Proof. exact (fun_ext (fun n : nat => @lem7991366 N s n)). Qed.
Lemma lem7991368 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991369 {N : Type'} (s : N -> Prop) : (term79 N s) = (term79 N s).
Proof. exact (MK_COMB (@lem7991368) (@lem7991367 N s)). Qed.
Lemma lem7991370 {N : Type'} : (term80 N) = (term80 N).
Proof. exact (fun_ext (fun s : N -> Prop => @lem7991369 N s)). Qed.
Lemma lem7991371 {N : Type'} : (@all (N -> Prop)) = (@all (N -> Prop)).
Proof. exact (eq_refl (@all (N -> Prop))). Qed.
Lemma lem7991372 {N : Type'} : (term10 N) = (term10 N).
Proof. exact (MK_COMB (@lem7991371 N) (@lem7991370 N)). Qed.
Lemma lem7991373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991374 {N : Type'} : (term44 N) = (term44 N).
Proof. exact (MK_COMB (@lem7991373) (@lem7991372 N)). Qed.
Lemma lem7991375 {A N : Type'} : (term46 A N) = (term46 A N).
Proof. exact (MK_COMB (@lem7991374 N) (@lem7991357 A N)). Qed.
Lemma lem7991384 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term77 A s n)) = ((@HAS_SIZE A s n) = (term77 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term77 A s n))). Qed.
Lemma lem7991385 {A : Type'} (s : A -> Prop) : (term78 A s) = (term78 A s).
Proof. exact (fun_ext (fun n : nat => @lem7991384 A s n)). Qed.
Lemma lem7991386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991387 {A : Type'} (s : A -> Prop) : (term79 A s) = (term79 A s).
Proof. exact (MK_COMB (@lem7991386) (@lem7991385 A s)). Qed.
Lemma lem7991388 {A : Type'} : (term80 A) = (term80 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7991387 A s)). Qed.
Lemma lem7991389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7991390 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7991389 A) (@lem7991388 A)). Qed.
Lemma lem7991391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991392 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (MK_COMB (@lem7991391) (@lem7991390 A)). Qed.
Lemma lem7991393 {A N : Type'} : (term48 A N) = (term48 A N).
Proof. exact (MK_COMB (@lem7991392 A) (@lem7991375 A N)). Qed.
Lemma lem7991402 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term77 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term77 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term77 _100044 s n))). Qed.
Lemma lem7991403 {_100044 : Type'} (s : _100044 -> Prop) : (term78 _100044 s) = (term78 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem7991402 _100044 s n)). Qed.
Lemma lem7991404 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991405 {_100044 : Type'} (s : _100044 -> Prop) : (term79 _100044 s) = (term79 _100044 s).
Proof. exact (MK_COMB (@lem7991404) (@lem7991403 _100044 s)). Qed.
Lemma lem7991406 {_100044 : Type'} : (term80 _100044) = (term80 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem7991405 _100044 s)). Qed.
Lemma lem7991407 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem7991408 {_100044 : Type'} : (term10 _100044) = (term10 _100044).
Proof. exact (MK_COMB (@lem7991407 _100044) (@lem7991406 _100044)). Qed.
Lemma lem7991409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7991410 {_100044 : Type'} : (term44 _100044) = (term44 _100044).
Proof. exact (MK_COMB (@lem7991409) (@lem7991408 _100044)). Qed.
Lemma lem7991411 {_100044 A N : Type'} : (term50 _100044 A N) = (term50 _100044 A N).
Proof. exact (MK_COMB (@lem7991410 _100044) (@lem7991393 A N)). Qed.
Lemma lem7991420 {A N : Type'} : (term51 A N) = (term51 A N).
Proof. exact (eq_refl (term51 A N)). Qed.
Lemma lem7991421 {_100044 A N : Type'} : (term52 _100044 A N) = (term52 _100044 A N).
Proof. exact (MK_COMB (@lem7991420 A N) (@lem7991411 _100044 A N)). Qed.
Lemma lem7991604 {_100044 A N : Type'} : (term13 _100044 A N) = (term52 _100044 A N).
Proof. exact (TRANS (@lem7991213 _100044 A N) (@lem7991421 _100044 A N)). Qed.
Lemma lem7991605 {_100044 A N : Type'} : (term52 _100044 A N) = (term13 _100044 A N).
Proof. exact (SYM (@lem7991604 _100044 A N)). Qed.
Lemma lem7991606 {A N : Type'} (h1 : term3 A N) : term3 A N.
Proof. exact (h1). Qed.
Lemma lem7991608 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem7991611 {A N : Type'} (h1 : term8 A N) : term8 A N.
Proof. exact (h1). Qed.
Lemma lem7991616 {A N : Type'} (h1 : term4 A N) : term4 A N.
Proof. exact (h1). Qed.
Lemma lem7991630 {A N : Type'} : (term3 A N) = (term81 A N).
Proof. exact (@lem17362 (@FINITE A (@UNIV A)) ((@CARD (cart A N) (@UNIV (cart A N))) = (term82 A N))). Qed.
Lemma lem7991939 {A : Type'} (s : A -> Prop) (n : nat) : (term83 A s n) = (term84 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem7991945 {A : Type'} (s : A -> Prop) (n : nat) : (term85 A s n) = (term85 A s n).
Proof. exact (eq_refl (term85 A s n)). Qed.
Lemma lem7991947 {A : Type'} (s : A -> Prop) (n : nat) : (term86 A s n) = (term86 A s n).
Proof. exact (eq_refl (term86 A s n)). Qed.
Lemma lem7991948 {A : Type'} (s : A -> Prop) (n : nat) : (term87 A s n) = (term88 A s n).
Proof. exact (MK_COMB (@lem7991947 A s n) (@lem7991939 A s n)). Qed.
Lemma lem7991949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7991950 {A : Type'} (s : A -> Prop) (n : nat) : (term89 A s n) = (term90 A s n).
Proof. exact (MK_COMB (@lem7991949) (@lem7991948 A s n)). Qed.
Lemma lem7991951 {A : Type'} (s : A -> Prop) (n : nat) : (term91 A s n) = (term92 A s n).
Proof. exact (MK_COMB (@lem7991950 A s n) (@lem7991945 A s n)). Qed.
Lemma lem7991952 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term77 A s n)) = (term91 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term77 A s n)). Qed.
Lemma lem7991953 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term77 A s n)) = (term92 A s n).
Proof. exact (TRANS (@lem7991952 A s n) (@lem7991951 A s n)). Qed.
Lemma lem7991954 {A : Type'} (s : A -> Prop) : (term78 A s) = (term93 A s).
Proof. exact (fun_ext (fun n : nat => @lem7991953 A s n)). Qed.
Lemma lem7991955 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991956 {A : Type'} (s : A -> Prop) : (term79 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem7991955) (@lem7991954 A s)). Qed.
Lemma lem7991957 {A : Type'} : (term80 A) = (term95 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7991956 A s)). Qed.
Lemma lem7991958 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7991959 {A : Type'} : (term10 A) = (term96 A).
Proof. exact (MK_COMB (@lem7991958 A) (@lem7991957 A)). Qed.
Lemma lem7991965 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7991966 (P : nat -> Prop) (Q : nat -> Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem7991965 nat P Q). Qed.
Lemma lem7991967 {A : Type'} (s : A -> Prop) : (term101 A s) = (term102 A s).
Proof. exact (@lem7991966 (term103 A s) (term104 A s)). Qed.
Lemma lem7991968 {A : Type'} (s : A -> Prop) (n : nat) : (term105 A s n) = (term88 A s n).
Proof. exact (eq_refl (term105 A s n)). Qed.
Lemma lem7991969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7991970 {A : Type'} (s : A -> Prop) (n : nat) : (term106 A s n) = (term90 A s n).
Proof. exact (MK_COMB (@lem7991969) (@lem7991968 A s n)). Qed.
Lemma lem7991971 {A : Type'} (s : A -> Prop) (n : nat) : (term107 A s n) = (term85 A s n).
Proof. exact (eq_refl (term107 A s n)). Qed.
Lemma lem7991972 {A : Type'} (s : A -> Prop) (n : nat) : (term108 A s n) = (term92 A s n).
Proof. exact (MK_COMB (@lem7991970 A s n) (@lem7991971 A s n)). Qed.
Lemma lem7991973 {A : Type'} (s : A -> Prop) : (term109 A s) = (term93 A s).
Proof. exact (fun_ext (fun n : nat => @lem7991972 A s n)). Qed.
Lemma lem7991974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991975 {A : Type'} (s : A -> Prop) : (term101 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem7991974) (@lem7991973 A s)). Qed.
Lemma lem7991976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7991977 {A : Type'} (s : A -> Prop) : (term110 A s) = (term111 A s).
Proof. exact (MK_COMB (@lem7991976) (@lem7991975 A s)). Qed.
Lemma lem7991978 {A : Type'} (s : A -> Prop) (n : nat) : (term105 A s n) = (term88 A s n).
Proof. exact (eq_refl (term105 A s n)). Qed.
Lemma lem7991979 {A : Type'} (s : A -> Prop) : (term112 A s) = (term103 A s).
Proof. exact (fun_ext (fun n : nat => @lem7991978 A s n)). Qed.
Lemma lem7991980 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991981 {A : Type'} (s : A -> Prop) : (term113 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem7991980) (@lem7991979 A s)). Qed.
Lemma lem7991982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7991983 {A : Type'} (s : A -> Prop) : (term115 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem7991982) (@lem7991981 A s)). Qed.
Lemma lem7991984 {A : Type'} (s : A -> Prop) (n : nat) : (term107 A s n) = (term85 A s n).
Proof. exact (eq_refl (term107 A s n)). Qed.
Lemma lem7991985 {A : Type'} (s : A -> Prop) : (term117 A s) = (term104 A s).
Proof. exact (fun_ext (fun n : nat => @lem7991984 A s n)). Qed.
Lemma lem7991986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7991987 {A : Type'} (s : A -> Prop) : (term118 A s) = (term119 A s).
Proof. exact (MK_COMB (@lem7991986) (@lem7991985 A s)). Qed.
Lemma lem7991988 {A : Type'} (s : A -> Prop) : (term102 A s) = (term120 A s).
Proof. exact (MK_COMB (@lem7991983 A s) (@lem7991987 A s)). Qed.
Lemma lem7991989 {A : Type'} (s : A -> Prop) : ((term101 A s) = (term102 A s)) = ((term94 A s) = (term120 A s)).
Proof. exact (MK_COMB (@lem7991977 A s) (@lem7991988 A s)). Qed.
Lemma lem7991990 {A : Type'} (s : A -> Prop) : (term94 A s) = (term120 A s).
Proof. exact (EQ_MP (@lem7991989 A s) (@lem7991967 A s)). Qed.
Lemma lem7992087 {A : Type'} : (term95 A) = (term121 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7991990 A s)). Qed.
Lemma lem7992088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7992089 {A : Type'} : (term96 A) = (term122 A).
Proof. exact (MK_COMB (@lem7992088 A) (@lem7992087 A)). Qed.
Lemma lem7992091 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7992092 {A : Type'} (P : type686 A) (Q : type686 A) : (term123 A P Q) = (term124 A P Q).
Proof. exact (@lem7992091 (A -> Prop) P Q). Qed.
Lemma lem7992093 {A : Type'} : (term125 A) = (term126 A).
Proof. exact (@lem7992092 A (term127 A) (term128 A)). Qed.
Lemma lem7992094 {A : Type'} (s : A -> Prop) : (term129 A s) = (term114 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem7992095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7992096 {A : Type'} (s : A -> Prop) : (term130 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem7992095) (@lem7992094 A s)). Qed.
Lemma lem7992097 {A : Type'} (s : A -> Prop) : (term131 A s) = (term119 A s).
Proof. exact (eq_refl (term131 A s)). Qed.
Lemma lem7992098 {A : Type'} (s : A -> Prop) : (term132 A s) = (term120 A s).
Proof. exact (MK_COMB (@lem7992096 A s) (@lem7992097 A s)). Qed.
Lemma lem7992099 {A : Type'} : (term133 A) = (term121 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7992098 A s)). Qed.
Lemma lem7992100 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7992101 {A : Type'} : (term125 A) = (term122 A).
Proof. exact (MK_COMB (@lem7992100 A) (@lem7992099 A)). Qed.
Lemma lem7992102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7992103 {A : Type'} : (term134 A) = (term135 A).
Proof. exact (MK_COMB (@lem7992102) (@lem7992101 A)). Qed.
Lemma lem7992104 {A : Type'} (s : A -> Prop) : (term129 A s) = (term114 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem7992105 {A : Type'} : (term136 A) = (term127 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7992104 A s)). Qed.
Lemma lem7992106 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7992107 {A : Type'} : (term137 A) = (term138 A).
Proof. exact (MK_COMB (@lem7992106 A) (@lem7992105 A)). Qed.
Lemma lem7992108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7992109 {A : Type'} : (term139 A) = (term140 A).
Proof. exact (MK_COMB (@lem7992108) (@lem7992107 A)). Qed.
Lemma lem7992110 {A : Type'} (s : A -> Prop) : (term131 A s) = (term119 A s).
Proof. exact (eq_refl (term131 A s)). Qed.
Lemma lem7992111 {A : Type'} : (term141 A) = (term128 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7992110 A s)). Qed.
Lemma lem7992112 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7992113 {A : Type'} : (term142 A) = (term143 A).
Proof. exact (MK_COMB (@lem7992112 A) (@lem7992111 A)). Qed.
Lemma lem7992114 {A : Type'} : (term126 A) = (term144 A).
Proof. exact (MK_COMB (@lem7992109 A) (@lem7992113 A)). Qed.
Lemma lem7992115 {A : Type'} : ((term125 A) = (term126 A)) = ((term122 A) = (term144 A)).
Proof. exact (MK_COMB (@lem7992103 A) (@lem7992114 A)). Qed.
Lemma lem7992116 {A : Type'} : (term122 A) = (term144 A).
Proof. exact (EQ_MP (@lem7992115 A) (@lem7992093 A)). Qed.
Lemma lem7992223 {A : Type'} : (term96 A) = (term144 A).
Proof. exact (TRANS (@lem7992089 A) (@lem7992116 A)). Qed.
Lemma lem7992224 {A : Type'} : (term10 A) = (term144 A).
Proof. exact (TRANS (@lem7991959 A) (@lem7992223 A)). Qed.
Lemma lem7992225 {A : Type'} (h1 : term10 A) : term144 A.
Proof. exact (EQ_MP (@lem7992224 A) (@lem7991608 A h1)). Qed.
Lemma lem7992830 {A N : Type'} (s : type24 A N) (n : nat) : (term145 A N s n) = (term146 A N s n).
Proof. exact (@lem17045 (@FINITE (cart A N) s) ((@CARD (cart A N) s) = n)). Qed.
Lemma lem7992836 {A N : Type'} (s : type24 A N) (n : nat) : (term147 A N s n) = (term147 A N s n).
Proof. exact (eq_refl (term147 A N s n)). Qed.
Lemma lem7992838 {A N : Type'} (s : type24 A N) (n : nat) : (term148 A N s n) = (term148 A N s n).
Proof. exact (eq_refl (term148 A N s n)). Qed.
Lemma lem7992839 {A N : Type'} (s : type24 A N) (n : nat) : (term149 A N s n) = (term150 A N s n).
Proof. exact (MK_COMB (@lem7992838 A N s n) (@lem7992830 A N s n)). Qed.
Lemma lem7992840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7992841 {A N : Type'} (s : type24 A N) (n : nat) : (term151 A N s n) = (term152 A N s n).
Proof. exact (MK_COMB (@lem7992840) (@lem7992839 A N s n)). Qed.
Lemma lem7992842 {A N : Type'} (s : type24 A N) (n : nat) : (term153 A N s n) = (term154 A N s n).
Proof. exact (MK_COMB (@lem7992841 A N s n) (@lem7992836 A N s n)). Qed.
Lemma lem7992843 {A N : Type'} (s : type24 A N) (n : nat) : ((@HAS_SIZE (cart A N) s n) = (term73 A N s n)) = (term153 A N s n).
Proof. exact (@lem17784 (@HAS_SIZE (cart A N) s n) (term73 A N s n)). Qed.
Lemma lem7992844 {A N : Type'} (s : type24 A N) (n : nat) : ((@HAS_SIZE (cart A N) s n) = (term73 A N s n)) = (term154 A N s n).
Proof. exact (TRANS (@lem7992843 A N s n) (@lem7992842 A N s n)). Qed.
Lemma lem7992845 {A N : Type'} (s : type24 A N) : (term74 A N s) = (term155 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7992844 A N s n)). Qed.
Lemma lem7992846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7992847 {A N : Type'} (s : type24 A N) : (term75 A N s) = (term156 A N s).
Proof. exact (MK_COMB (@lem7992846) (@lem7992845 A N s)). Qed.
Lemma lem7992848 {A N : Type'} : (term76 A N) = (term157 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7992847 A N s)). Qed.
Lemma lem7992849 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7992850 {A N : Type'} : (term8 A N) = (term158 A N).
Proof. exact (MK_COMB (@lem7992849 A N) (@lem7992848 A N)). Qed.
Lemma lem7992856 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7992857 (P : nat -> Prop) (Q : nat -> Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem7992856 nat P Q). Qed.
Lemma lem7992858 {A N : Type'} (s : type24 A N) : (term159 A N s) = (term160 A N s).
Proof. exact (@lem7992857 (term161 A N s) (term162 A N s)). Qed.
Lemma lem7992859 {A N : Type'} (s : type24 A N) (n : nat) : (term163 A N s n) = (term150 A N s n).
Proof. exact (eq_refl (term163 A N s n)). Qed.
Lemma lem7992860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7992861 {A N : Type'} (s : type24 A N) (n : nat) : (term164 A N s n) = (term152 A N s n).
Proof. exact (MK_COMB (@lem7992860) (@lem7992859 A N s n)). Qed.
Lemma lem7992862 {A N : Type'} (s : type24 A N) (n : nat) : (term165 A N s n) = (term147 A N s n).
Proof. exact (eq_refl (term165 A N s n)). Qed.
Lemma lem7992863 {A N : Type'} (s : type24 A N) (n : nat) : (term166 A N s n) = (term154 A N s n).
Proof. exact (MK_COMB (@lem7992861 A N s n) (@lem7992862 A N s n)). Qed.
Lemma lem7992864 {A N : Type'} (s : type24 A N) : (term167 A N s) = (term155 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7992863 A N s n)). Qed.
Lemma lem7992865 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7992866 {A N : Type'} (s : type24 A N) : (term159 A N s) = (term156 A N s).
Proof. exact (MK_COMB (@lem7992865) (@lem7992864 A N s)). Qed.
Lemma lem7992867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7992868 {A N : Type'} (s : type24 A N) : (term168 A N s) = (term169 A N s).
Proof. exact (MK_COMB (@lem7992867) (@lem7992866 A N s)). Qed.
Lemma lem7992869 {A N : Type'} (s : type24 A N) (n : nat) : (term163 A N s n) = (term150 A N s n).
Proof. exact (eq_refl (term163 A N s n)). Qed.
Lemma lem7992870 {A N : Type'} (s : type24 A N) : (term170 A N s) = (term161 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7992869 A N s n)). Qed.
Lemma lem7992871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7992872 {A N : Type'} (s : type24 A N) : (term171 A N s) = (term172 A N s).
Proof. exact (MK_COMB (@lem7992871) (@lem7992870 A N s)). Qed.
Lemma lem7992873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7992874 {A N : Type'} (s : type24 A N) : (term173 A N s) = (term174 A N s).
Proof. exact (MK_COMB (@lem7992873) (@lem7992872 A N s)). Qed.
Lemma lem7992875 {A N : Type'} (s : type24 A N) (n : nat) : (term165 A N s n) = (term147 A N s n).
Proof. exact (eq_refl (term165 A N s n)). Qed.
Lemma lem7992876 {A N : Type'} (s : type24 A N) : (term175 A N s) = (term162 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7992875 A N s n)). Qed.
Lemma lem7992877 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7992878 {A N : Type'} (s : type24 A N) : (term176 A N s) = (term177 A N s).
Proof. exact (MK_COMB (@lem7992877) (@lem7992876 A N s)). Qed.
Lemma lem7992879 {A N : Type'} (s : type24 A N) : (term160 A N s) = (term178 A N s).
Proof. exact (MK_COMB (@lem7992874 A N s) (@lem7992878 A N s)). Qed.
Lemma lem7992880 {A N : Type'} (s : type24 A N) : ((term159 A N s) = (term160 A N s)) = ((term156 A N s) = (term178 A N s)).
Proof. exact (MK_COMB (@lem7992868 A N s) (@lem7992879 A N s)). Qed.
Lemma lem7992881 {A N : Type'} (s : type24 A N) : (term156 A N s) = (term178 A N s).
Proof. exact (EQ_MP (@lem7992880 A N s) (@lem7992858 A N s)). Qed.
Lemma lem7992978 {A N : Type'} : (term157 A N) = (term179 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7992881 A N s)). Qed.
Lemma lem7992979 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7992980 {A N : Type'} : (term158 A N) = (term180 A N).
Proof. exact (MK_COMB (@lem7992979 A N) (@lem7992978 A N)). Qed.
Lemma lem7992982 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7992983 {A N : Type'} (P : type56 A N) (Q : type56 A N) : (term181 A N P Q) = (term182 A N P Q).
Proof. exact (@lem7992982 (type24 A N) P Q). Qed.
Lemma lem7992984 {A N : Type'} : (term183 A N) = (term184 A N).
Proof. exact (@lem7992983 A N (term185 A N) (term186 A N)). Qed.
Lemma lem7992985 {A N : Type'} (s : type24 A N) : (term187 A N s) = (term172 A N s).
Proof. exact (eq_refl (term187 A N s)). Qed.
Lemma lem7992986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7992987 {A N : Type'} (s : type24 A N) : (term188 A N s) = (term174 A N s).
Proof. exact (MK_COMB (@lem7992986) (@lem7992985 A N s)). Qed.
Lemma lem7992988 {A N : Type'} (s : type24 A N) : (term189 A N s) = (term177 A N s).
Proof. exact (eq_refl (term189 A N s)). Qed.
Lemma lem7992989 {A N : Type'} (s : type24 A N) : (term190 A N s) = (term178 A N s).
Proof. exact (MK_COMB (@lem7992987 A N s) (@lem7992988 A N s)). Qed.
Lemma lem7992990 {A N : Type'} : (term191 A N) = (term179 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7992989 A N s)). Qed.
Lemma lem7992991 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7992992 {A N : Type'} : (term183 A N) = (term180 A N).
Proof. exact (MK_COMB (@lem7992991 A N) (@lem7992990 A N)). Qed.
Lemma lem7992993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7992994 {A N : Type'} : (term192 A N) = (term193 A N).
Proof. exact (MK_COMB (@lem7992993) (@lem7992992 A N)). Qed.
Lemma lem7992995 {A N : Type'} (s : type24 A N) : (term187 A N s) = (term172 A N s).
Proof. exact (eq_refl (term187 A N s)). Qed.
Lemma lem7992996 {A N : Type'} : (term194 A N) = (term185 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7992995 A N s)). Qed.
Lemma lem7992997 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7992998 {A N : Type'} : (term195 A N) = (term196 A N).
Proof. exact (MK_COMB (@lem7992997 A N) (@lem7992996 A N)). Qed.
Lemma lem7992999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7993000 {A N : Type'} : (term197 A N) = (term198 A N).
Proof. exact (MK_COMB (@lem7992999) (@lem7992998 A N)). Qed.
Lemma lem7993001 {A N : Type'} (s : type24 A N) : (term189 A N s) = (term177 A N s).
Proof. exact (eq_refl (term189 A N s)). Qed.
Lemma lem7993002 {A N : Type'} : (term199 A N) = (term186 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7993001 A N s)). Qed.
Lemma lem7993003 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7993004 {A N : Type'} : (term200 A N) = (term201 A N).
Proof. exact (MK_COMB (@lem7993003 A N) (@lem7993002 A N)). Qed.
Lemma lem7993005 {A N : Type'} : (term184 A N) = (term202 A N).
Proof. exact (MK_COMB (@lem7993000 A N) (@lem7993004 A N)). Qed.
Lemma lem7993006 {A N : Type'} : ((term183 A N) = (term184 A N)) = ((term180 A N) = (term202 A N)).
Proof. exact (MK_COMB (@lem7992994 A N) (@lem7993005 A N)). Qed.
Lemma lem7993007 {A N : Type'} : (term180 A N) = (term202 A N).
Proof. exact (EQ_MP (@lem7993006 A N) (@lem7992984 A N)). Qed.
Lemma lem7993114 {A N : Type'} : (term158 A N) = (term202 A N).
Proof. exact (TRANS (@lem7992980 A N) (@lem7993007 A N)). Qed.
Lemma lem7993115 {A N : Type'} : (term8 A N) = (term202 A N).
Proof. exact (TRANS (@lem7992850 A N) (@lem7993114 A N)). Qed.
Lemma lem7993116 {A N : Type'} (h1 : term8 A N) : term202 A N.
Proof. exact (EQ_MP (@lem7993115 A N) (@lem7991611 A N h1)). Qed.
Lemma lem7994077 {A N : Type'} (m : nat) : (term59 A N m) = (term203 A N m).
Proof. exact (@lem17265 (@HAS_SIZE A (@UNIV A) m) (term204 A N m)). Qed.
Lemma lem7994078 {A N : Type'} : (term60 A N) = (term205 A N).
Proof. exact (fun_ext (fun m : nat => @lem7994077 A N m)). Qed.
Lemma lem7994079 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7994132 {A N : Type'} : (term4 A N) = (term206 A N).
Proof. exact (MK_COMB (@lem7994079) (@lem7994078 A N)). Qed.
Lemma lem7994133 {A N : Type'} (h1 : term4 A N) : term206 A N.
Proof. exact (EQ_MP (@lem7994132 A N) (@lem7991616 A N h1)). Qed.
Lemma lem7994346 {A N : Type'} (h1 : term3 A N) : term81 A N.
Proof. exact (EQ_MP (@lem7991630 A N) (@lem7991606 A N h1)). Qed.
Lemma lem7994433 {A : Type'} (s : A -> Prop) (n : nat) : (term85 A s n) = (term85 A s n).
Proof. exact (eq_refl (term85 A s n)). Qed.
Lemma lem7994434 {A : Type'} (s : A -> Prop) : (term104 A s) = (term104 A s).
Proof. exact (fun_ext (fun n : nat => @lem7994433 A s n)). Qed.
Lemma lem7994435 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7994436 {A : Type'} (s : A -> Prop) : (term119 A s) = (term119 A s).
Proof. exact (MK_COMB (@lem7994435) (@lem7994434 A s)). Qed.
Lemma lem7994437 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7994436 A s)). Qed.
Lemma lem7994438 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7994439 {A : Type'} : (term143 A) = (term143 A).
Proof. exact (MK_COMB (@lem7994438 A) (@lem7994437 A)). Qed.
Lemma lem7994464 {A : Type'} (s : A -> Prop) (n : nat) : (term88 A s n) = (term88 A s n).
Proof. exact (eq_refl (term88 A s n)). Qed.
Lemma lem7994465 {A : Type'} (s : A -> Prop) : (term103 A s) = (term103 A s).
Proof. exact (fun_ext (fun n : nat => @lem7994464 A s n)). Qed.
Lemma lem7994466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7994467 {A : Type'} (s : A -> Prop) : (term114 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem7994466) (@lem7994465 A s)). Qed.
Lemma lem7994468 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7994467 A s)). Qed.
Lemma lem7994469 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7994470 {A : Type'} : (term138 A) = (term138 A).
Proof. exact (MK_COMB (@lem7994469 A) (@lem7994468 A)). Qed.
Lemma lem7994471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7994472 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (MK_COMB (@lem7994471) (@lem7994470 A)). Qed.
Lemma lem7994473 {A : Type'} : (term144 A) = (term144 A).
Proof. exact (MK_COMB (@lem7994472 A) (@lem7994439 A)). Qed.
Lemma lem7994474 {A : Type'} (h1 : term10 A) : term144 A.
Proof. exact (EQ_MP (@lem7994473 A) (@lem7992225 A h1)). Qed.
Lemma lem7994625 {A N : Type'} (s : type24 A N) (n : nat) : (term147 A N s n) = (term147 A N s n).
Proof. exact (eq_refl (term147 A N s n)). Qed.
Lemma lem7994626 {A N : Type'} (s : type24 A N) : (term162 A N s) = (term162 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7994625 A N s n)). Qed.
Lemma lem7994627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7994628 {A N : Type'} (s : type24 A N) : (term177 A N s) = (term177 A N s).
Proof. exact (MK_COMB (@lem7994627) (@lem7994626 A N s)). Qed.
Lemma lem7994629 {A N : Type'} : (term186 A N) = (term186 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7994628 A N s)). Qed.
Lemma lem7994630 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7994631 {A N : Type'} : (term201 A N) = (term201 A N).
Proof. exact (MK_COMB (@lem7994630 A N) (@lem7994629 A N)). Qed.
Lemma lem7994656 {A N : Type'} (s : type24 A N) (n : nat) : (term150 A N s n) = (term150 A N s n).
Proof. exact (eq_refl (term150 A N s n)). Qed.
Lemma lem7994657 {A N : Type'} (s : type24 A N) : (term161 A N s) = (term161 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7994656 A N s n)). Qed.
Lemma lem7994658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7994659 {A N : Type'} (s : type24 A N) : (term172 A N s) = (term172 A N s).
Proof. exact (MK_COMB (@lem7994658) (@lem7994657 A N s)). Qed.
Lemma lem7994660 {A N : Type'} : (term185 A N) = (term185 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7994659 A N s)). Qed.
Lemma lem7994661 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7994662 {A N : Type'} : (term196 A N) = (term196 A N).
Proof. exact (MK_COMB (@lem7994661 A N) (@lem7994660 A N)). Qed.
Lemma lem7994663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7994664 {A N : Type'} : (term198 A N) = (term198 A N).
Proof. exact (MK_COMB (@lem7994663) (@lem7994662 A N)). Qed.
Lemma lem7994665 {A N : Type'} : (term202 A N) = (term202 A N).
Proof. exact (MK_COMB (@lem7994664 A N) (@lem7994631 A N)). Qed.
Lemma lem7994666 {A N : Type'} (h1 : term8 A N) : term202 A N.
Proof. exact (EQ_MP (@lem7994665 A N) (@lem7993116 A N h1)). Qed.
Lemma lem7994904 {A N : Type'} (m : nat) : (term203 A N m) = (term203 A N m).
Proof. exact (eq_refl (term203 A N m)). Qed.
Lemma lem7994905 {A N : Type'} : (term205 A N) = (term205 A N).
Proof. exact (fun_ext (fun m : nat => @lem7994904 A N m)). Qed.
Lemma lem7994906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7994907 {A N : Type'} : (term206 A N) = (term206 A N).
Proof. exact (MK_COMB (@lem7994906) (@lem7994905 A N)). Qed.
Lemma lem7994908 {A N : Type'} (h1 : term4 A N) : term206 A N.
Proof. exact (EQ_MP (@lem7994907 A N) (@lem7994133 A N h1)). Qed.
Lemma lem7994990 {A N : Type'} (h1 : term8 A N) : term201 A N.
Proof. exact (proj2 (@lem7994666 A N h1)). Qed.
Lemma lem7994997 {A : Type'} (h1 : term10 A) : term138 A.
Proof. exact (proj1 (@lem7994474 A h1)). Qed.
Lemma lem7995022 {A N : Type'} (m : nat) : (term203 A N m) = (term203 A N m).
Proof. exact (eq_refl (term203 A N m)). Qed.
Lemma lem7995023 {A N : Type'} : (term205 A N) = (term205 A N).
Proof. exact (fun_ext (fun m : nat => @lem7995022 A N m)). Qed.
Lemma lem7995024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7995026 {A N : Type'} : (term206 A N) = (term206 A N).
Proof. exact (MK_COMB (@lem7995024) (@lem7995023 A N)). Qed.
Lemma lem7995027 {A N : Type'} (h1 : term4 A N) : term206 A N.
Proof. exact (EQ_MP (@lem7995026 A N) (@lem7994908 A N h1)). Qed.
Lemma lem7995250 {A N : Type'} (s : type24 A N) (n : nat) : (term147 A N s n) = (term207 A N s n).
Proof. exact (@lem19490 (@FINITE (cart A N) s) (term208 A N s n) ((@CARD (cart A N) s) = n)). Qed.
Lemma lem7995251 {A N : Type'} (s : type24 A N) : (term162 A N s) = (term209 A N s).
Proof. exact (fun_ext (fun n : nat => @lem7995250 A N s n)). Qed.
Lemma lem7995252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7995253 {A N : Type'} (s : type24 A N) : (term177 A N s) = (term210 A N s).
Proof. exact (MK_COMB (@lem7995252) (@lem7995251 A N s)). Qed.
Lemma lem7995254 {A N : Type'} : (term186 A N) = (term211 A N).
Proof. exact (fun_ext (fun s : type24 A N => @lem7995253 A N s)). Qed.
Lemma lem7995255 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem7995257 {A N : Type'} : (term201 A N) = (term212 A N).
Proof. exact (MK_COMB (@lem7995255 A N) (@lem7995254 A N)). Qed.
Lemma lem7995258 {A N : Type'} (h1 : term8 A N) : term212 A N.
Proof. exact (EQ_MP (@lem7995257 A N) (@lem7994990 A N h1)). Qed.
Lemma lem7995368 {A : Type'} (s : A -> Prop) (n : nat) : (term88 A s n) = (term88 A s n).
Proof. exact (eq_refl (term88 A s n)). Qed.
Lemma lem7995369 {A : Type'} (s : A -> Prop) : (term103 A s) = (term103 A s).
Proof. exact (fun_ext (fun n : nat => @lem7995368 A s n)). Qed.
Lemma lem7995370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7995371 {A : Type'} (s : A -> Prop) : (term114 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem7995370) (@lem7995369 A s)). Qed.
Lemma lem7995372 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7995371 A s)). Qed.
Lemma lem7995373 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7995375 {A : Type'} : (term138 A) = (term138 A).
Proof. exact (MK_COMB (@lem7995373 A) (@lem7995372 A)). Qed.
Lemma lem7995376 {A : Type'} (h1 : term10 A) : term138 A.
Proof. exact (EQ_MP (@lem7995375 A) (@lem7994997 A h1)). Qed.
Lemma lem7995462 {A N : Type'} (_105408 : nat) (h1 : term4 A N) : term213 A N _105408.
Proof. exact (@lem7995027 A N h1 _105408). Qed.
Lemma lem7995463 {A N : Type'} (_105408 : nat) : (term213 A N _105408) = (term203 A N _105408).
Proof. exact (eq_refl (term213 A N _105408)). Qed.
Lemma lem7995516 {A N : Type'} (_105426 : type24 A N) (h1 : term8 A N) : term214 A N _105426.
Proof. exact (@lem7995258 A N h1 _105426). Qed.
Lemma lem7995517 {A N : Type'} (_105426 : type24 A N) : (term214 A N _105426) = (term210 A N _105426).
Proof. exact (eq_refl (term214 A N _105426)). Qed.
Lemma lem7995518 {A N : Type'} (_105426 : type24 A N) (h1 : term8 A N) : term210 A N _105426.
Proof. exact (EQ_MP (@lem7995517 A N _105426) (@lem7995516 A N _105426 h1)). Qed.
Lemma lem7995519 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) (h1 : term8 A N) : term215 A N _105426 _105427.
Proof. exact (@lem7995518 A N _105426 h1 _105427). Qed.
Lemma lem7995520 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term215 A N _105426 _105427) = (term207 A N _105426 _105427).
Proof. exact (eq_refl (term215 A N _105426 _105427)). Qed.
Lemma lem7995521 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) (h1 : term8 A N) : term207 A N _105426 _105427.
Proof. exact (EQ_MP (@lem7995520 A N _105426 _105427) (@lem7995519 A N _105426 _105427 h1)). Qed.
Lemma lem7995546 {A : Type'} (_105436 : A -> Prop) (h1 : term10 A) : term129 A _105436.
Proof. exact (@lem7995376 A h1 _105436). Qed.
Lemma lem7995547 {A : Type'} (_105436 : A -> Prop) : (term129 A _105436) = (term114 A _105436).
Proof. exact (eq_refl (term129 A _105436)). Qed.
Lemma lem7995548 {A : Type'} (_105436 : A -> Prop) (h1 : term10 A) : term114 A _105436.
Proof. exact (EQ_MP (@lem7995547 A _105436) (@lem7995546 A _105436 h1)). Qed.
Lemma lem7995549 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) (h1 : term10 A) : term105 A _105436 _105437.
Proof. exact (@lem7995548 A _105436 h1 _105437). Qed.
Lemma lem7995550 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term105 A _105436 _105437) = (term88 A _105436 _105437).
Proof. exact (eq_refl (term105 A _105436 _105437)). Qed.
Lemma lem7995597 {A N : Type'} (_105408 : nat) (h1 : term4 A N) : term203 A N _105408.
Proof. exact (EQ_MP (@lem7995463 A N _105408) (@lem7995462 A N _105408 h1)). Qed.
Lemma lem7995685 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) (h1 : term10 A) : term88 A _105436 _105437.
Proof. exact (EQ_MP (@lem7995550 A _105436 _105437) (@lem7995549 A _105436 _105437 h1)). Qed.
Lemma lem7995699 {A N : Type'} (h1 : term3 A N) : term216 A N.
Proof. exact (proj2 (@lem7994346 A N h1)). Qed.
Lemma lem7995759 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) (h1 : term8 A N) : term217 A N _105426 _105427.
Proof. exact (proj2 (@lem7995521 A N _105426 _105427 h1)). Qed.
Lemma lem7996166 {A N : Type'} (h1 : term3 A N) : @FINITE A (@UNIV A).
Proof. exact (proj1 (@lem7994346 A N h1)). Qed.
Lemma lem7996167 {A N : Type'} (h1 : term3 A N) : term218 A.
Proof. exact (fun h0 : term219 A => @lem7996166 A N h1). Qed.
Lemma lem7996169 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7996170 {A : Type'} : (term218 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem7996169 (@FINITE A (@UNIV A))). Qed.
Lemma lem7996171 {A N : Type'} (h1 : term3 A N) : @FINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem7996170 A) (@lem7996167 A N h1)). Qed.
Lemma lem7996173 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem7996174 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (@lem7996173 (@CARD A (@UNIV A))). Qed.
Lemma lem7996175 {A : Type'} : term221 A.
Proof. exact (fun h0 : term222 A => @lem7996174 A). Qed.
Lemma lem7996177 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7996178 {A : Type'} : (term221 A) = ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A))).
Proof. exact (@lem7996177 ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A)))). Qed.
Lemma lem7996179 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (EQ_MP (@lem7996178 A) (@lem7996175 A)). Qed.
Lemma lem7996181 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7996182 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term88 A _105436 _105437) = (term224 A _105436 _105437).
Proof. exact (@lem7996181 (term84 A _105436 _105437) (@HAS_SIZE A _105436 _105437)). Qed.
Lemma lem7996184 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7996185 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term227 A _105436 _105437) = (term228 A _105436 _105437).
Proof. exact (@lem7996184 (term229 A _105436) (term230 A _105436 _105437)). Qed.
Lemma lem7996187 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7996188 {A : Type'} (_105436 : A -> Prop) : (term232 A _105436) = (@FINITE A _105436).
Proof. exact (@lem7996187 (@FINITE A _105436)). Qed.
Lemma lem7996189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7996190 {A : Type'} (_105436 : A -> Prop) : (term233 A _105436) = (term234 A _105436).
Proof. exact (MK_COMB (@lem7996189) (@lem7996188 A _105436)). Qed.
Lemma lem7996192 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7996193 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term235 A _105436 _105437) = ((@CARD A _105436) = _105437).
Proof. exact (@lem7996192 ((@CARD A _105436) = _105437)). Qed.
Lemma lem7996194 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term228 A _105436 _105437) = (term77 A _105436 _105437).
Proof. exact (MK_COMB (@lem7996190 A _105436) (@lem7996193 A _105436 _105437)). Qed.
Lemma lem7996195 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term227 A _105436 _105437) = (term77 A _105436 _105437).
Proof. exact (TRANS (@lem7996185 A _105436 _105437) (@lem7996194 A _105436 _105437)). Qed.
Lemma lem7996196 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996197 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term236 A _105436 _105437) = (term237 A _105436 _105437).
Proof. exact (MK_COMB (@lem7996196) (@lem7996195 A _105436 _105437)). Qed.
Lemma lem7996198 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (@HAS_SIZE A _105436 _105437) = (@HAS_SIZE A _105436 _105437).
Proof. exact (eq_refl (@HAS_SIZE A _105436 _105437)). Qed.
Lemma lem7996199 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term224 A _105436 _105437) = (term238 A _105436 _105437).
Proof. exact (MK_COMB (@lem7996197 A _105436 _105437) (@lem7996198 A _105436 _105437)). Qed.
Lemma lem7996200 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) : (term88 A _105436 _105437) = (term238 A _105436 _105437).
Proof. exact (TRANS (@lem7996182 A _105436 _105437) (@lem7996199 A _105436 _105437)). Qed.
Lemma lem7996202 {A N : Type'} (h1 : term3 A N) : term239 A.
Proof. exact (conj (@lem7996171 A N h1) (@lem7996179 A)). Qed.
Lemma lem7996204 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) (h1 : term10 A) : term238 A _105436 _105437.
Proof. exact (EQ_MP (@lem7996200 A _105436 _105437) (@lem7995685 A _105436 _105437 h1)). Qed.
Lemma lem7996205 {A : Type'} (_105436 : A -> Prop) (_105437 : nat) (h1 : term10 A) : term238 A _105436 _105437.
Proof. exact (@lem7996204 A _105436 _105437 h1). Qed.
Lemma lem7996206 {A : Type'} (h1 : term10 A) : term240 A.
Proof. exact (@lem7996205 A (@UNIV A) (@CARD A (@UNIV A)) h1). Qed.
Lemma lem7996209 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term241 A.
Proof. exact (@lem7996206 A h1 (@lem7996202 A N h2)). Qed.
Lemma lem7996210 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term242 A.
Proof. exact (fun h0 : term243 A => @lem7996209 A N h1 h2). Qed.
Lemma lem7996212 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7996213 {A : Type'} : (term242 A) = (term241 A).
Proof. exact (@lem7996212 (term241 A)). Qed.
Lemma lem7996214 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term241 A.
Proof. exact (EQ_MP (@lem7996213 A) (@lem7996210 A N h1 h2)). Qed.
Lemma lem7996220 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7996221 {A N : Type'} (_105408 : nat) : (term203 A N _105408) = (term244 A N _105408).
Proof. exact (@lem7996220 (term204 A N _105408) (term245 A _105408)). Qed.
Lemma lem7996227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7996228 {A N : Type'} (_105408 : nat) : (term246 A N _105408) = (term247 A N _105408).
Proof. exact (MK_COMB (@lem7996227) (@lem7996221 A N _105408)). Qed.
Lemma lem7996234 {A N : Type'} (_105408 : nat) : (term244 A N _105408) = (term244 A N _105408).
Proof. exact (eq_refl (term244 A N _105408)). Qed.
Lemma lem7996235 {A N : Type'} (_105408 : nat) : ((term203 A N _105408) = (term244 A N _105408)) = ((term244 A N _105408) = (term244 A N _105408)).
Proof. exact (MK_COMB (@lem7996228 A N _105408) (@lem7996234 A N _105408)). Qed.
Lemma lem7996237 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7996238 (x : Prop) : (x = x) = True.
Proof. exact (@lem7996237 Prop x). Qed.
Lemma lem7996239 {A N : Type'} (_105408 : nat) : ((term244 A N _105408) = (term244 A N _105408)) = True.
Proof. exact (@lem7996238 (term244 A N _105408)). Qed.
Lemma lem7996240 {A N : Type'} (_105408 : nat) : ((term203 A N _105408) = (term244 A N _105408)) = True.
Proof. exact (TRANS (@lem7996235 A N _105408) (@lem7996239 A N _105408)). Qed.
Lemma lem7996241 {A N : Type'} (_105408 : nat) : True = ((term203 A N _105408) = (term244 A N _105408)).
Proof. exact (SYM (@lem7996240 A N _105408)). Qed.
Lemma lem7996242 {A N : Type'} (_105408 : nat) : (term203 A N _105408) = (term244 A N _105408).
Proof. exact (EQ_MP (@lem7996241 A N _105408) (@lem0)). Qed.
Lemma lem7996243 {A N : Type'} (_105408 : nat) (h1 : term4 A N) : term244 A N _105408.
Proof. exact (EQ_MP (@lem7996242 A N _105408) (@lem7995597 A N _105408 h1)). Qed.
Lemma lem7996245 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7996246 {A N : Type'} (_105408 : nat) : (term244 A N _105408) = (term248 A N _105408).
Proof. exact (@lem7996245 (term245 A _105408) (term204 A N _105408)). Qed.
Lemma lem7996248 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7996249 {A : Type'} (_105408 : nat) : (term249 A _105408) = (@HAS_SIZE A (@UNIV A) _105408).
Proof. exact (@lem7996248 (@HAS_SIZE A (@UNIV A) _105408)). Qed.
Lemma lem7996250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996251 {A : Type'} (_105408 : nat) : (term250 A _105408) = (term251 A _105408).
Proof. exact (MK_COMB (@lem7996250) (@lem7996249 A _105408)). Qed.
Lemma lem7996252 {A N : Type'} (_105408 : nat) : (term204 A N _105408) = (term204 A N _105408).
Proof. exact (eq_refl (term204 A N _105408)). Qed.
Lemma lem7996253 {A N : Type'} (_105408 : nat) : (term248 A N _105408) = (term59 A N _105408).
Proof. exact (MK_COMB (@lem7996251 A _105408) (@lem7996252 A N _105408)). Qed.
Lemma lem7996254 {A N : Type'} (_105408 : nat) : (term244 A N _105408) = (term59 A N _105408).
Proof. exact (TRANS (@lem7996246 A N _105408) (@lem7996253 A N _105408)). Qed.
Lemma lem7996257 {A N : Type'} (_105408 : nat) (h1 : term4 A N) : term59 A N _105408.
Proof. exact (EQ_MP (@lem7996254 A N _105408) (@lem7996243 A N _105408 h1)). Qed.
Lemma lem7996258 {A N : Type'} (h1 : term4 A N) : term252 A N.
Proof. exact (@lem7996257 A N (@CARD A (@UNIV A)) h1). Qed.
Lemma lem7996261 {A N : Type'} (h1 : term10 A) (h2 : term4 A N) (h3 : term3 A N) : term253 A N.
Proof. exact (@lem7996258 A N h2 (@lem7996214 A N h1 h3)). Qed.
Lemma lem7996262 {A N : Type'} (h1 : term10 A) (h2 : term4 A N) (h3 : term3 A N) : term254 A N.
Proof. exact (fun h0 : term255 A N => @lem7996261 A N h1 h2 h3). Qed.
Lemma lem7996264 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7996265 {A N : Type'} : (term254 A N) = (term253 A N).
Proof. exact (@lem7996264 (term253 A N)). Qed.
Lemma lem7996266 {A N : Type'} (h1 : term10 A) (h2 : term4 A N) (h3 : term3 A N) : term253 A N.
Proof. exact (EQ_MP (@lem7996265 A N) (@lem7996262 A N h1 h2 h3)). Qed.
Lemma lem7996272 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7996273 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term217 A N _105426 _105427) = (term256 A N _105426 _105427).
Proof. exact (@lem7996272 ((@CARD (cart A N) _105426) = _105427) (term208 A N _105426 _105427)). Qed.
Lemma lem7996281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7996282 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term257 A N _105426 _105427) = (term258 A N _105426 _105427).
Proof. exact (MK_COMB (@lem7996281) (@lem7996273 A N _105426 _105427)). Qed.
Lemma lem7996290 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term256 A N _105426 _105427) = (term256 A N _105426 _105427).
Proof. exact (eq_refl (term256 A N _105426 _105427)). Qed.
Lemma lem7996291 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : ((term217 A N _105426 _105427) = (term256 A N _105426 _105427)) = ((term256 A N _105426 _105427) = (term256 A N _105426 _105427)).
Proof. exact (MK_COMB (@lem7996282 A N _105426 _105427) (@lem7996290 A N _105426 _105427)). Qed.
Lemma lem7996293 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7996294 (x : Prop) : (x = x) = True.
Proof. exact (@lem7996293 Prop x). Qed.
Lemma lem7996295 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : ((term256 A N _105426 _105427) = (term256 A N _105426 _105427)) = True.
Proof. exact (@lem7996294 (term256 A N _105426 _105427)). Qed.
Lemma lem7996296 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : ((term217 A N _105426 _105427) = (term256 A N _105426 _105427)) = True.
Proof. exact (TRANS (@lem7996291 A N _105426 _105427) (@lem7996295 A N _105426 _105427)). Qed.
Lemma lem7996297 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : True = ((term217 A N _105426 _105427) = (term256 A N _105426 _105427)).
Proof. exact (SYM (@lem7996296 A N _105426 _105427)). Qed.
Lemma lem7996298 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term217 A N _105426 _105427) = (term256 A N _105426 _105427).
Proof. exact (EQ_MP (@lem7996297 A N _105426 _105427) (@lem0)). Qed.
Lemma lem7996299 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) (h1 : term8 A N) : term256 A N _105426 _105427.
Proof. exact (EQ_MP (@lem7996298 A N _105426 _105427) (@lem7995759 A N _105426 _105427 h1)). Qed.
Lemma lem7996301 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7996302 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term256 A N _105426 _105427) = (term259 A N _105426 _105427).
Proof. exact (@lem7996301 (term208 A N _105426 _105427) ((@CARD (cart A N) _105426) = _105427)). Qed.
Lemma lem7996304 (a : Prop) : (term231 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7996305 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term260 A N _105426 _105427) = (@HAS_SIZE (cart A N) _105426 _105427).
Proof. exact (@lem7996304 (@HAS_SIZE (cart A N) _105426 _105427)). Qed.
Lemma lem7996306 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7996307 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term261 A N _105426 _105427) = (term262 A N _105426 _105427).
Proof. exact (MK_COMB (@lem7996306) (@lem7996305 A N _105426 _105427)). Qed.
Lemma lem7996308 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : ((@CARD (cart A N) _105426) = _105427) = ((@CARD (cart A N) _105426) = _105427).
Proof. exact (eq_refl ((@CARD (cart A N) _105426) = _105427)). Qed.
Lemma lem7996309 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term259 A N _105426 _105427) = (term263 A N _105426 _105427).
Proof. exact (MK_COMB (@lem7996307 A N _105426 _105427) (@lem7996308 A N _105426 _105427)). Qed.
Lemma lem7996310 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) : (term256 A N _105426 _105427) = (term263 A N _105426 _105427).
Proof. exact (TRANS (@lem7996302 A N _105426 _105427) (@lem7996309 A N _105426 _105427)). Qed.
Lemma lem7996313 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) (h1 : term8 A N) : term263 A N _105426 _105427.
Proof. exact (EQ_MP (@lem7996310 A N _105426 _105427) (@lem7996299 A N _105426 _105427 h1)). Qed.
Lemma lem7996314 {A N : Type'} (_105426 : type24 A N) (_105427 : nat) (h1 : term8 A N) : term263 A N _105426 _105427.
Proof. exact (@lem7996313 A N _105426 _105427 h1). Qed.
Lemma lem7996315 {A N : Type'} (h1 : term8 A N) : term264 A N.
Proof. exact (@lem7996314 A N (@UNIV (cart A N)) (term82 A N) h1). Qed.
Lemma lem7996318 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : (@CARD (cart A N) (@UNIV (cart A N))) = (term82 A N).
Proof. exact (@lem7996315 A N h2 (@lem7996266 A N h1 h3 h4)). Qed.
Lemma lem7996319 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term265 A N.
Proof. exact (fun h0 : term216 A N => @lem7996318 A N h1 h2 h3 h4). Qed.
Lemma lem7996321 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7996322 {A N : Type'} : (term265 A N) = ((@CARD (cart A N) (@UNIV (cart A N))) = (term82 A N)).
Proof. exact (@lem7996321 ((@CARD (cart A N) (@UNIV (cart A N))) = (term82 A N))). Qed.
Lemma lem7996323 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : (@CARD (cart A N) (@UNIV (cart A N))) = (term82 A N).
Proof. exact (EQ_MP (@lem7996322 A N) (@lem7996319 A N h1 h2 h3 h4)). Qed.
Lemma lem7996326 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7996328 {A N : Type'} : (term216 A N) = (term266 A N).
Proof. exact (@lem7996326 ((@CARD (cart A N) (@UNIV (cart A N))) = (term82 A N))). Qed.
Lemma lem7996331 {A N : Type'} (h1 : term3 A N) : term266 A N.
Proof. exact (EQ_MP (@lem7996328 A N) (@lem7995699 A N h1)). Qed.
Lemma lem7996334 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : False.
Proof. exact (@lem7996331 A N h4 (@lem7996323 A N h1 h2 h3 h4)). Qed.
Lemma lem7996335 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term267.
Proof. exact (fun h0 : ~ False => @lem7996334 A N h1 h2 h3 h4). Qed.
Lemma lem7996337 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7996338 : term267 = False.
Proof. exact (@lem7996337 False). Qed.
Lemma lem7996339 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : False.
Proof. exact (EQ_MP (@lem7996338) (@lem7996335 A N h1 h2 h3 h4)). Qed.
Lemma lem7996340 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term17 A N.
Proof. exact (fun h0 : term5 A N => @lem7996339 A N h1 h2 h3 h4). Qed.
Lemma lem7996341 {A N : Type'} : (term17 A N) = (term18 A N).
Proof. exact (@lem69 (term5 A N)). Qed.
Lemma lem7996342 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term18 A N.
Proof. exact (EQ_MP (@lem7996341 A N) (@lem7996340 A N h1 h2 h3 h4)). Qed.
Lemma lem7996343 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term21 A N.
Proof. exact (fun h0 : term6 N => @lem7996342 A N h1 h2 h3 h4). Qed.
Lemma lem7996344 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term4 A N) (h4 : term3 A N) : term24 A N.
Proof. exact (fun h0 : term7 A N => @lem7996343 A N h1 h2 h3 h4). Qed.
Lemma lem7996345 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term27 A N.
Proof. exact (fun h0 : term4 A N => @lem7996344 A N h1 h2 h0 h3). Qed.
Lemma lem7996346 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term29 A N.
Proof. exact (fun h0 : term6 A => @lem7996345 A N h1 h2 h3). Qed.
Lemma lem7996347 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term32 A N.
Proof. exact (fun h0 : term9 A N => @lem7996346 A N h1 h2 h3). Qed.
Lemma lem7996348 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term35 A N.
Proof. exact (fun h0 : term11 N => @lem7996347 A N h1 h2 h3). Qed.
Lemma lem7996349 {A N : Type'} (h1 : term10 A) (h2 : term8 A N) (h3 : term3 A N) : term38 A N.
Proof. exact (fun h0 : term12 A N => @lem7996348 A N h1 h2 h3). Qed.
Lemma lem7996350 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term41 A N.
Proof. exact (fun h0 : term8 A N => @lem7996349 A N h1 h0 h2). Qed.
Lemma lem7996351 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term43 A N.
Proof. exact (fun h0 : term11 A => @lem7996350 A N h1 h2). Qed.
Lemma lem7996352 {A N : Type'} (h1 : term10 A) (h2 : term3 A N) : term46 A N.
Proof. exact (fun h0 : term10 N => @lem7996351 A N h1 h2). Qed.
Lemma lem7996353 {A N : Type'} (h1 : term3 A N) : term48 A N.
Proof. exact (fun h0 : term10 A => @lem7996352 A N h0 h1). Qed.
Lemma lem7996354 {_100044 A N : Type'} (h1 : term3 A N) : term50 _100044 A N.
Proof. exact (fun h0 : term10 _100044 => @lem7996353 A N h1). Qed.
Lemma lem7996355 {_100044 A N : Type'} : term52 _100044 A N.
Proof. exact (fun h0 : term3 A N => @lem7996354 _100044 A N h0). Qed.
Lemma lem7996356 {_100044 A N : Type'} : term13 _100044 A N.
Proof. exact (EQ_MP (@lem7991605 _100044 A N) (@lem7996355 _100044 A N)). Qed.
Lemma lem7996358 {_100044 A N : Type'} : term13 _100044 A N.
Proof. exact (@lem7991016 _100044 A N (@lem7996356 _100044 A N)). Qed.
Lemma lem7996359 {_100044 A N : Type'} (h1 : term3 A N) : term49 _100044 A N.
Proof. exact (@lem7996358 _100044 A N (@lem7990982 A N h1)). Qed.
Lemma lem7996360 {A N : Type'} (h1 : term3 A N) : term47 A N.
Proof. exact (@lem7996359 Prop A N h1 (@lem3863773 Prop)). Qed.
Lemma lem7996361 {A N : Type'} (h1 : term3 A N) : term45 A N.
Proof. exact (@lem7996360 A N h1 (@lem7990995 A)). Qed.
Lemma lem7996362 {A N : Type'} (h1 : term3 A N) : term42 A N.
Proof. exact (@lem7996361 A N h1 (@lem7990993 N)). Qed.
Lemma lem7996363 {A N : Type'} (h1 : term3 A N) : term40 A N.
Proof. exact (@lem7996362 A N h1 (@lem7990997 A)). Qed.
Lemma lem7996364 {A N : Type'} (h1 : term3 A N) : term37 A N.
Proof. exact (@lem7996363 A N h1 (@lem7990991 A N)). Qed.
Lemma lem7996365 {A N : Type'} (h1 : term3 A N) : term34 A N.
Proof. exact (@lem7996364 A N h1 (@lem7990996 A N)). Qed.
Lemma lem7996366 {A N : Type'} (h1 : term3 A N) : term31 A N.
Proof. exact (@lem7996365 A N h1 (@lem7990994 N)). Qed.
Lemma lem7996367 {A N : Type'} (h1 : term3 A N) : term28 A N.
Proof. exact (@lem7996366 A N h1 (@lem7990992 A N)). Qed.
Lemma lem7996368 {A N : Type'} (h1 : term3 A N) : term26 A N.
Proof. exact (@lem7996367 A N h1 (@lem7990988 A)). Qed.
Lemma lem7996369 {A N : Type'} (h1 : term3 A N) : term23 A N.
Proof. exact (@lem7996368 A N h1 (@lem7990983 A N)). Qed.
Lemma lem7996370 {A N : Type'} (h1 : term3 A N) : term20 A N.
Proof. exact (@lem7996369 A N h1 (@lem7990989 A N)). Qed.
Lemma lem7996371 {A N : Type'} (h1 : term3 A N) : term17 A N.
Proof. exact (@lem7996370 A N h1 (@lem7990985 N)). Qed.
Lemma lem7996372 {A N : Type'} (h1 : term3 A N) : False.
Proof. exact (@lem7996371 A N h1 (@lem7990984 A N)). Qed.
Lemma lem7996373 {A N : Type'} (h1 : term3 A N) : (term3 A N) = False.
Proof. exact (prop_ext (fun h2 : term3 A N => @lem7996372 A N h1) (fun h2 : False => @lem7990982 A N h1)). Qed.
Lemma lem7996374 {A N : Type'} (h1 : term3 A N) : False.
Proof. exact (EQ_MP (@lem7996373 A N h1) (@lem7990982 A N h1)). Qed.
Lemma lem7996375 {A N : Type'} : term2 A N.
Proof. exact (fun h0 : term3 A N => @lem7996374 A N h0). Qed.
Lemma lem7996376 {A N : Type'} : term1 A N.
Proof. exact (EQ_MP (@lem7990981 A N) (@lem7996375 A N)). Qed.
