Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_UNIONS_NONEMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem3476183 {_89711 _89725 : Type'} : term0 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem3476184 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term1 _89711 _89725 P.
Proof. exact (@lem3476183 _89711 _89725 P). Qed.
Lemma lem3476185 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term1 _89711 _89725 P) = (term2 _89711 _89725 P).
Proof. exact (eq_refl (term1 _89711 _89725 P)). Qed.
Lemma lem3476186 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term2 _89711 _89725 P.
Proof. exact (EQ_MP (@lem3476185 _89711 _89725 P) (@lem3476184 _89711 _89725 P)). Qed.
Lemma lem3476187 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term3 _89711 _89725 P f.
Proof. exact (@lem3476186 _89711 _89725 P f). Qed.
Lemma lem3476188 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term3 _89711 _89725 P f) = ((term4 _89711 _89725 P f) = (term5 _89711 _89725 P f)).
Proof. exact (eq_refl (term3 _89711 _89725 P f)). Qed.
Lemma lem3476205 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term4 _89711 _89725 P f) = (term5 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem3476188 _89711 _89725 P f) (@lem3476187 _89711 _89725 P f)). Qed.
Lemma lem3476206 {_90228 : Type'} (P : type686 _90228) (f : type672 _90228) : (term6 _90228 P f) = (term7 _90228 P f).
Proof. exact (@lem3476205 _90228 (_90228 -> Prop) P f). Qed.
Lemma lem3476207 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term8 _90228 s u) = (term9 _90228 s u).
Proof. exact (@lem3476206 _90228 (term10 _90228 s) (term11 _90228 u)). Qed.
Lemma lem3476208 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) : (term12 _90228 s t) = (@IN (_90228 -> Prop) t s).
Proof. exact (eq_refl (term12 _90228 s t)). Qed.
Lemma lem3476209 {_90228 : Type'} (GEN_PVAR_69 : _90228 -> Prop) : (@SETSPEC (_90228 -> Prop) GEN_PVAR_69) = (@SETSPEC (_90228 -> Prop) GEN_PVAR_69).
Proof. exact (eq_refl (@SETSPEC (_90228 -> Prop) GEN_PVAR_69)). Qed.
Lemma lem3476210 {_90228 : Type'} (GEN_PVAR_69 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) : (term13 _90228 GEN_PVAR_69 s t) = (term14 _90228 GEN_PVAR_69 t s).
Proof. exact (MK_COMB (@lem3476209 _90228 GEN_PVAR_69) (@lem3476208 _90228 t s)). Qed.
Lemma lem3476211 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) : (term15 _90228 u t) = (@DIFF _90228 u t).
Proof. exact (eq_refl (term15 _90228 u t)). Qed.
Lemma lem3476212 {_90228 : Type'} (GEN_PVAR_69 : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) : (term16 _90228 GEN_PVAR_69 s u t) = (term17 _90228 GEN_PVAR_69 s u t).
Proof. exact (MK_COMB (@lem3476210 _90228 GEN_PVAR_69 t s) (@lem3476211 _90228 u t)). Qed.
Lemma lem3476213 {_90228 : Type'} (GEN_PVAR_69 : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) : (term18 _90228 GEN_PVAR_69 s u) = (term19 _90228 GEN_PVAR_69 s u).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476212 _90228 GEN_PVAR_69 s u t)). Qed.
Lemma lem3476214 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3476215 {_90228 : Type'} (GEN_PVAR_69 : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) : (term20 _90228 GEN_PVAR_69 s u) = (term21 _90228 GEN_PVAR_69 s u).
Proof. exact (MK_COMB (@lem3476214 _90228) (@lem3476213 _90228 GEN_PVAR_69 s u)). Qed.
Lemma lem3476216 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term22 _90228 s u) = (term23 _90228 s u).
Proof. exact (fun_ext (fun GEN_PVAR_69 : _90228 -> Prop => @lem3476215 _90228 GEN_PVAR_69 s u)). Qed.
Lemma lem3476217 {_90228 : Type'} : (@GSPEC (_90228 -> Prop)) = (@GSPEC (_90228 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_90228 -> Prop))). Qed.
Lemma lem3476218 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term24 _90228 s u) = (term25 _90228 s u).
Proof. exact (MK_COMB (@lem3476217 _90228) (@lem3476216 _90228 s u)). Qed.
Lemma lem3476219 {_90228 : Type'} : (@INTERS _90228) = (@INTERS _90228).
Proof. exact (eq_refl (@INTERS _90228)). Qed.
Lemma lem3476220 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term8 _90228 s u) = (term26 _90228 s u).
Proof. exact (MK_COMB (@lem3476219 _90228) (@lem3476218 _90228 s u)). Qed.
Lemma lem3476221 {_90228 : Type'} : (@eq (_90228 -> Prop)) = (@eq (_90228 -> Prop)).
Proof. exact (eq_refl (@eq (_90228 -> Prop))). Qed.
Lemma lem3476222 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term27 _90228 s u) = (term28 _90228 s u).
Proof. exact (MK_COMB (@lem3476221 _90228) (@lem3476220 _90228 s u)). Qed.
Lemma lem3476223 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) : (term12 _90228 s t) = (@IN (_90228 -> Prop) t s).
Proof. exact (eq_refl (term12 _90228 s t)). Qed.
Lemma lem3476224 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3476225 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) : (term29 _90228 s t) = (term30 _90228 t s).
Proof. exact (MK_COMB (@lem3476224) (@lem3476223 _90228 t s)). Qed.
Lemma lem3476226 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) : (term15 _90228 u t) = (@DIFF _90228 u t).
Proof. exact (eq_refl (term15 _90228 u t)). Qed.
Lemma lem3476227 {_90228 : Type'} (a : _90228) : (@IN _90228 a) = (@IN _90228 a).
Proof. exact (eq_refl (@IN _90228 a)). Qed.
Lemma lem3476228 {_90228 : Type'} (a : _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) : (term31 _90228 a u t) = (term32 _90228 a u t).
Proof. exact (MK_COMB (@lem3476227 _90228 a) (@lem3476226 _90228 u t)). Qed.
Lemma lem3476229 {_90228 : Type'} (s : type686 _90228) (a : _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) : (term33 _90228 s a u t) = (term34 _90228 s a u t).
Proof. exact (MK_COMB (@lem3476225 _90228 t s) (@lem3476228 _90228 a u t)). Qed.
Lemma lem3476230 {_90228 : Type'} (s : type686 _90228) (a : _90228) (u : _90228 -> Prop) : (term35 _90228 s a u) = (term36 _90228 s a u).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476229 _90228 s a u t)). Qed.
Lemma lem3476231 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476232 {_90228 : Type'} (s : type686 _90228) (a : _90228) (u : _90228 -> Prop) : (term37 _90228 s a u) = (term38 _90228 s a u).
Proof. exact (MK_COMB (@lem3476231 _90228) (@lem3476230 _90228 s a u)). Qed.
Lemma lem3476233 {_90228 : Type'} (GEN_PVAR_56 : _90228) : (@SETSPEC _90228 GEN_PVAR_56) = (@SETSPEC _90228 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _90228 GEN_PVAR_56)). Qed.
Lemma lem3476234 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (a : _90228) (u : _90228 -> Prop) : (term39 _90228 GEN_PVAR_56 s a u) = (term40 _90228 GEN_PVAR_56 s a u).
Proof. exact (MK_COMB (@lem3476233 _90228 GEN_PVAR_56) (@lem3476232 _90228 s a u)). Qed.
Lemma lem3476235 {_90228 : Type'} (a : _90228) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3476236 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (u : _90228 -> Prop) (a : _90228) : (term41 _90228 GEN_PVAR_56 s u a) = (term42 _90228 GEN_PVAR_56 s u a).
Proof. exact (MK_COMB (@lem3476234 _90228 GEN_PVAR_56 s a u) (@lem3476235 _90228 a)). Qed.
Lemma lem3476237 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (u : _90228 -> Prop) : (term43 _90228 GEN_PVAR_56 s u) = (term44 _90228 GEN_PVAR_56 s u).
Proof. exact (fun_ext (fun a : _90228 => @lem3476236 _90228 GEN_PVAR_56 s u a)). Qed.
Lemma lem3476238 {_90228 : Type'} : (@ex _90228) = (@ex _90228).
Proof. exact (eq_refl (@ex _90228)). Qed.
Lemma lem3476239 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (u : _90228 -> Prop) : (term45 _90228 GEN_PVAR_56 s u) = (term46 _90228 GEN_PVAR_56 s u).
Proof. exact (MK_COMB (@lem3476238 _90228) (@lem3476237 _90228 GEN_PVAR_56 s u)). Qed.
Lemma lem3476240 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term47 _90228 s u) = (term48 _90228 s u).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _90228 => @lem3476239 _90228 GEN_PVAR_56 s u)). Qed.
Lemma lem3476241 {_90228 : Type'} : (@GSPEC _90228) = (@GSPEC _90228).
Proof. exact (eq_refl (@GSPEC _90228)). Qed.
Lemma lem3476242 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term9 _90228 s u) = (term49 _90228 s u).
Proof. exact (MK_COMB (@lem3476241 _90228) (@lem3476240 _90228 s u)). Qed.
Lemma lem3476243 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : ((term8 _90228 s u) = (term9 _90228 s u)) = ((term26 _90228 s u) = (term49 _90228 s u)).
Proof. exact (MK_COMB (@lem3476222 _90228 s u) (@lem3476242 _90228 s u)). Qed.
Lemma lem3476244 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term26 _90228 s u) = (term49 _90228 s u).
Proof. exact (EQ_MP (@lem3476243 _90228 s u) (@lem3476207 _90228 s u)). Qed.
Lemma lem3476255 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) : (term50 _90228 u s) = (term50 _90228 u s).
Proof. exact (eq_refl (term50 _90228 u s)). Qed.
Lemma lem3476256 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : ((term51 _90228 u s) = (term26 _90228 s u)) = ((term51 _90228 u s) = (term49 _90228 s u)).
Proof. exact (MK_COMB (@lem3476255 _90228 u s) (@lem3476244 _90228 s u)). Qed.
Lemma lem3476259 {_90228 : Type'} (s : type686 _90228) : (term52 _90228 s) = (term52 _90228 s).
Proof. exact (eq_refl (term52 _90228 s)). Qed.
Lemma lem3476260 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term53 _90228 s u) = (term54 _90228 s u).
Proof. exact (MK_COMB (@lem3476259 _90228 s) (@lem3476256 _90228 s u)). Qed.
Lemma lem3476263 {_90228 : Type'} (u : _90228 -> Prop) : (term55 _90228 u) = (term56 _90228 u).
Proof. exact (fun_ext (fun s : type686 _90228 => @lem3476260 _90228 s u)). Qed.
Lemma lem3476264 {_90228 : Type'} : (@all ((_90228 -> Prop) -> Prop)) = (@all ((_90228 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90228 -> Prop) -> Prop))). Qed.
Lemma lem3476265 {_90228 : Type'} (u : _90228 -> Prop) : (term57 _90228 u) = (term58 _90228 u).
Proof. exact (MK_COMB (@lem3476264 _90228) (@lem3476263 _90228 u)). Qed.
Lemma lem3476270 {_90228 : Type'} : (term59 _90228) = (term60 _90228).
Proof. exact (fun_ext (fun u : _90228 -> Prop => @lem3476265 _90228 u)). Qed.
Lemma lem3476271 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476272 {_90228 : Type'} : (term61 _90228) = (term62 _90228).
Proof. exact (MK_COMB (@lem3476271 _90228) (@lem3476270 _90228)). Qed.
Lemma lem3476277 {_90228 : Type'} : (term62 _90228) = (term61 _90228).
Proof. exact (SYM (@lem3476272 _90228)). Qed.
Lemma lem3476291 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term63 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3476292 {_90228 : Type'} (s : type686 _90228) (t : type686 _90228) : (s = t) = (term64 _90228 s t).
Proof. exact (@lem3476291 (_90228 -> Prop) s t). Qed.
Lemma lem3476293 {_90228 : Type'} (s : type686 _90228) : (s = (@EMPTY (_90228 -> Prop))) = (term65 _90228 s).
Proof. exact (@lem3476292 _90228 s (@EMPTY (_90228 -> Prop))). Qed.
Lemma lem3476302 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476303 {_90228 : Type'} (s : type686 _90228) : (term66 _90228 s) = (term67 _90228 s).
Proof. exact (MK_COMB (@lem3476302) (@lem3476293 _90228 s)). Qed.
Lemma lem3476304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3476305 {_90228 : Type'} (s : type686 _90228) : (term52 _90228 s) = (term68 _90228 s).
Proof. exact (MK_COMB (@lem3476304) (@lem3476303 _90228 s)). Qed.
Lemma lem3476309 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term63 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3476310 {_90228 : Type'} (s : _90228 -> Prop) (t : _90228 -> Prop) : (s = t) = (term63 _90228 s t).
Proof. exact (@lem3476309 _90228 s t). Qed.
Lemma lem3476311 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : ((term51 _90228 u s) = (term49 _90228 s u)) = (term69 _90228 s u).
Proof. exact (@lem3476310 _90228 (term51 _90228 u s) (term49 _90228 s u)). Qed.
Lemma lem3476330 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term54 _90228 s u) = (term70 _90228 s u).
Proof. exact (MK_COMB (@lem3476305 _90228 s) (@lem3476311 _90228 s u)). Qed.
Lemma lem3476333 {_90228 : Type'} (u : _90228 -> Prop) : (term56 _90228 u) = (term71 _90228 u).
Proof. exact (fun_ext (fun s : type686 _90228 => @lem3476330 _90228 s u)). Qed.
Lemma lem3476334 {_90228 : Type'} : (@all ((_90228 -> Prop) -> Prop)) = (@all ((_90228 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90228 -> Prop) -> Prop))). Qed.
Lemma lem3476335 {_90228 : Type'} (u : _90228 -> Prop) : (term58 _90228 u) = (term72 _90228 u).
Proof. exact (MK_COMB (@lem3476334 _90228) (@lem3476333 _90228 u)). Qed.
Lemma lem3476340 {_90228 : Type'} : (term60 _90228) = (term73 _90228).
Proof. exact (fun_ext (fun u : _90228 -> Prop => @lem3476335 _90228 u)). Qed.
Lemma lem3476341 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476342 {_90228 : Type'} : (term62 _90228) = (term74 _90228).
Proof. exact (MK_COMB (@lem3476341 _90228) (@lem3476340 _90228)). Qed.
Lemma lem3476347 {_90228 : Type'} : (term74 _90228) = (term62 _90228).
Proof. exact (SYM (@lem3476342 _90228)). Qed.
Lemma lem3476365 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3476366 {_90228 : Type'} (P : type686 _90228) (x : _90228 -> Prop) : (@IN (_90228 -> Prop) x P) = (P x).
Proof. exact (@lem3476365 (_90228 -> Prop) P x). Qed.
Lemma lem3476367 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : (@IN (_90228 -> Prop) x s) = (s x).
Proof. exact (@lem3476366 _90228 s x). Qed.
Lemma lem3476368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3476369 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : (term75 _90228 x s) = (term76 _90228 s x).
Proof. exact (MK_COMB (@lem3476368) (@lem3476367 _90228 s x)). Qed.
Lemma lem3476371 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3476372 {_90228 : Type'} (x : _90228 -> Prop) : (@IN (_90228 -> Prop) x (@EMPTY (_90228 -> Prop))) = False.
Proof. exact (@lem3476371 (_90228 -> Prop) x). Qed.
Lemma lem3476373 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : ((@IN (_90228 -> Prop) x s) = (@IN (_90228 -> Prop) x (@EMPTY (_90228 -> Prop)))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3476369 _90228 s x) (@lem3476372 _90228 x)). Qed.
Lemma lem3476375 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3476376 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : ((s x) = False) = (term77 _90228 s x).
Proof. exact (@lem3476375 (s x)). Qed.
Lemma lem3476377 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : ((@IN (_90228 -> Prop) x s) = (@IN (_90228 -> Prop) x (@EMPTY (_90228 -> Prop)))) = (term77 _90228 s x).
Proof. exact (TRANS (@lem3476373 _90228 s x) (@lem3476376 _90228 s x)). Qed.
Lemma lem3476378 {_90228 : Type'} (s : type686 _90228) : (term78 _90228 s) = (term79 _90228 s).
Proof. exact (fun_ext (fun x : _90228 -> Prop => @lem3476377 _90228 s x)). Qed.
Lemma lem3476379 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476380 {_90228 : Type'} (s : type686 _90228) : (term65 _90228 s) = (term80 _90228 s).
Proof. exact (MK_COMB (@lem3476379 _90228) (@lem3476378 _90228 s)). Qed.
Lemma lem3476385 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476386 {_90228 : Type'} (s : type686 _90228) : (term67 _90228 s) = (term81 _90228 s).
Proof. exact (MK_COMB (@lem3476385) (@lem3476380 _90228 s)). Qed.
Lemma lem3476387 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3476388 {_90228 : Type'} (s : type686 _90228) : (term68 _90228 s) = (term82 _90228 s).
Proof. exact (MK_COMB (@lem3476387) (@lem3476386 _90228 s)). Qed.
Lemma lem3476396 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term83 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3476397 {_90228 : Type'} (s : _90228 -> Prop) (x : _90228) (t : _90228 -> Prop) : (term32 _90228 x s t) = (term83 _90228 s x t).
Proof. exact (@lem3476396 _90228 s x t). Qed.
Lemma lem3476398 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) : (term84 _90228 x u s) = (term85 _90228 u x s).
Proof. exact (@lem3476397 _90228 u x (@UNIONS _90228 s)). Qed.
Lemma lem3476402 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3476403 {_90228 : Type'} (P : _90228 -> Prop) (x : _90228) : (@IN _90228 x P) = (P x).
Proof. exact (@lem3476402 _90228 P x). Qed.
Lemma lem3476404 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (@IN _90228 x u) = (u x).
Proof. exact (@lem3476403 _90228 u x). Qed.
Lemma lem3476405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3476406 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term86 _90228 x u) = (term87 _90228 u x).
Proof. exact (MK_COMB (@lem3476405) (@lem3476404 _90228 u x)). Qed.
Lemma lem3476408 {A : Type'} (s : type686 A) (x : A) : (term88 A x s) = (term89 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3476409 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term88 _90228 x s) = (term89 _90228 s x).
Proof. exact (@lem3476408 _90228 s x). Qed.
Lemma lem3476417 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3476418 {_90228 : Type'} (P : type686 _90228) (x : _90228 -> Prop) : (@IN (_90228 -> Prop) x P) = (P x).
Proof. exact (@lem3476417 (_90228 -> Prop) P x). Qed.
Lemma lem3476419 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (@IN (_90228 -> Prop) t s) = (s t).
Proof. exact (@lem3476418 _90228 s t). Qed.
Lemma lem3476420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3476421 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term90 _90228 t s) = (term91 _90228 s t).
Proof. exact (MK_COMB (@lem3476420) (@lem3476419 _90228 s t)). Qed.
Lemma lem3476423 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3476424 {_90228 : Type'} (P : _90228 -> Prop) (x : _90228) : (@IN _90228 x P) = (P x).
Proof. exact (@lem3476423 _90228 P x). Qed.
Lemma lem3476425 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (@IN _90228 x t) = (t x).
Proof. exact (@lem3476424 _90228 t x). Qed.
Lemma lem3476426 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term92 _90228 s x t) = (term93 _90228 s t x).
Proof. exact (MK_COMB (@lem3476421 _90228 s t) (@lem3476425 _90228 t x)). Qed.
Lemma lem3476429 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term94 _90228 s x) = (term95 _90228 s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476426 _90228 s t x)). Qed.
Lemma lem3476430 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3476431 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term89 _90228 s x) = (term96 _90228 s x).
Proof. exact (MK_COMB (@lem3476430 _90228) (@lem3476429 _90228 s x)). Qed.
Lemma lem3476436 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term88 _90228 x s) = (term96 _90228 s x).
Proof. exact (TRANS (@lem3476409 _90228 s x) (@lem3476431 _90228 s x)). Qed.
Lemma lem3476437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476438 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term97 _90228 x s) = (term98 _90228 s x).
Proof. exact (MK_COMB (@lem3476437) (@lem3476436 _90228 s x)). Qed.
Lemma lem3476439 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term85 _90228 u x s) = (term99 _90228 u s x).
Proof. exact (MK_COMB (@lem3476406 _90228 u x) (@lem3476438 _90228 s x)). Qed.
Lemma lem3476442 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term84 _90228 x u s) = (term99 _90228 u s x).
Proof. exact (TRANS (@lem3476398 _90228 u x s) (@lem3476439 _90228 u s x)). Qed.
Lemma lem3476443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3476444 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term100 _90228 x u s) = (term101 _90228 u s x).
Proof. exact (MK_COMB (@lem3476443) (@lem3476442 _90228 u s x)). Qed.
Lemma lem3476446 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term102 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3476447 {_90228 : Type'} (p : _90228 -> Prop) (x : _90228) : (term102 _90228 x p) = (p x).
Proof. exact (@lem3476446 _90228 p x). Qed.
Lemma lem3476448 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term103 _90228 x s u) = (term104 _90228 s u x).
Proof. exact (@lem3476447 _90228 (term105 _90228 s u) x). Qed.
Lemma lem3476449 {_90228 : Type'} (s : type686 _90228) (a : _90228) (u : _90228 -> Prop) : (term104 _90228 s u a) = (term38 _90228 s a u).
Proof. exact (eq_refl (term104 _90228 s u a)). Qed.
Lemma lem3476450 {_90228 : Type'} (GEN_PVAR_56 : _90228) : (@SETSPEC _90228 GEN_PVAR_56) = (@SETSPEC _90228 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _90228 GEN_PVAR_56)). Qed.
Lemma lem3476451 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (a : _90228) (u : _90228 -> Prop) : (term106 _90228 GEN_PVAR_56 s u a) = (term40 _90228 GEN_PVAR_56 s a u).
Proof. exact (MK_COMB (@lem3476450 _90228 GEN_PVAR_56) (@lem3476449 _90228 s a u)). Qed.
Lemma lem3476452 {_90228 : Type'} (a : _90228) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3476453 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (u : _90228 -> Prop) (a : _90228) : (term107 _90228 GEN_PVAR_56 s u a) = (term42 _90228 GEN_PVAR_56 s u a).
Proof. exact (MK_COMB (@lem3476451 _90228 GEN_PVAR_56 s a u) (@lem3476452 _90228 a)). Qed.
Lemma lem3476454 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (u : _90228 -> Prop) : (term108 _90228 GEN_PVAR_56 s u) = (term44 _90228 GEN_PVAR_56 s u).
Proof. exact (fun_ext (fun a : _90228 => @lem3476453 _90228 GEN_PVAR_56 s u a)). Qed.
Lemma lem3476455 {_90228 : Type'} : (@ex _90228) = (@ex _90228).
Proof. exact (eq_refl (@ex _90228)). Qed.
Lemma lem3476456 {_90228 : Type'} (GEN_PVAR_56 : _90228) (s : type686 _90228) (u : _90228 -> Prop) : (term109 _90228 GEN_PVAR_56 s u) = (term46 _90228 GEN_PVAR_56 s u).
Proof. exact (MK_COMB (@lem3476455 _90228) (@lem3476454 _90228 GEN_PVAR_56 s u)). Qed.
Lemma lem3476457 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term110 _90228 s u) = (term48 _90228 s u).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _90228 => @lem3476456 _90228 GEN_PVAR_56 s u)). Qed.
Lemma lem3476458 {_90228 : Type'} : (@GSPEC _90228) = (@GSPEC _90228).
Proof. exact (eq_refl (@GSPEC _90228)). Qed.
Lemma lem3476459 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term111 _90228 s u) = (term49 _90228 s u).
Proof. exact (MK_COMB (@lem3476458 _90228) (@lem3476457 _90228 s u)). Qed.
Lemma lem3476460 {_90228 : Type'} (x : _90228) : (@IN _90228 x) = (@IN _90228 x).
Proof. exact (eq_refl (@IN _90228 x)). Qed.
Lemma lem3476461 {_90228 : Type'} (x : _90228) (s : type686 _90228) (u : _90228 -> Prop) : (term103 _90228 x s u) = (term112 _90228 x s u).
Proof. exact (MK_COMB (@lem3476460 _90228 x) (@lem3476459 _90228 s u)). Qed.
Lemma lem3476462 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3476463 {_90228 : Type'} (x : _90228) (s : type686 _90228) (u : _90228 -> Prop) : (term113 _90228 x s u) = (term114 _90228 x s u).
Proof. exact (MK_COMB (@lem3476462) (@lem3476461 _90228 x s u)). Qed.
Lemma lem3476464 {_90228 : Type'} (s : type686 _90228) (x : _90228) (u : _90228 -> Prop) : (term104 _90228 s u x) = (term38 _90228 s x u).
Proof. exact (eq_refl (term104 _90228 s u x)). Qed.
Lemma lem3476465 {_90228 : Type'} (s : type686 _90228) (x : _90228) (u : _90228 -> Prop) : ((term103 _90228 x s u) = (term104 _90228 s u x)) = ((term112 _90228 x s u) = (term38 _90228 s x u)).
Proof. exact (MK_COMB (@lem3476463 _90228 x s u) (@lem3476464 _90228 s x u)). Qed.
Lemma lem3476466 {_90228 : Type'} (s : type686 _90228) (x : _90228) (u : _90228 -> Prop) : (term112 _90228 x s u) = (term38 _90228 s x u).
Proof. exact (EQ_MP (@lem3476465 _90228 s x u) (@lem3476448 _90228 s u x)). Qed.
Lemma lem3476474 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3476475 {_90228 : Type'} (P : type686 _90228) (x : _90228 -> Prop) : (@IN (_90228 -> Prop) x P) = (P x).
Proof. exact (@lem3476474 (_90228 -> Prop) P x). Qed.
Lemma lem3476476 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (@IN (_90228 -> Prop) t s) = (s t).
Proof. exact (@lem3476475 _90228 s t). Qed.
Lemma lem3476477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3476478 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term30 _90228 t s) = (term115 _90228 s t).
Proof. exact (MK_COMB (@lem3476477) (@lem3476476 _90228 s t)). Qed.
Lemma lem3476480 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term83 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3476481 {_90228 : Type'} (s : _90228 -> Prop) (x : _90228) (t : _90228 -> Prop) : (term32 _90228 x s t) = (term83 _90228 s x t).
Proof. exact (@lem3476480 _90228 s x t). Qed.
Lemma lem3476482 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (t : _90228 -> Prop) : (term32 _90228 x u t) = (term83 _90228 u x t).
Proof. exact (@lem3476481 _90228 u x t). Qed.
Lemma lem3476486 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3476487 {_90228 : Type'} (P : _90228 -> Prop) (x : _90228) : (@IN _90228 x P) = (P x).
Proof. exact (@lem3476486 _90228 P x). Qed.
Lemma lem3476488 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (@IN _90228 x u) = (u x).
Proof. exact (@lem3476487 _90228 u x). Qed.
Lemma lem3476489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3476490 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term86 _90228 x u) = (term87 _90228 u x).
Proof. exact (MK_COMB (@lem3476489) (@lem3476488 _90228 u x)). Qed.
Lemma lem3476492 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3476493 {_90228 : Type'} (P : _90228 -> Prop) (x : _90228) : (@IN _90228 x P) = (P x).
Proof. exact (@lem3476492 _90228 P x). Qed.
Lemma lem3476494 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (@IN _90228 x t) = (t x).
Proof. exact (@lem3476493 _90228 t x). Qed.
Lemma lem3476495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476496 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (term116 _90228 x t) = (term117 _90228 t x).
Proof. exact (MK_COMB (@lem3476495) (@lem3476494 _90228 t x)). Qed.
Lemma lem3476497 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term83 _90228 u x t) = (term118 _90228 u t x).
Proof. exact (MK_COMB (@lem3476490 _90228 u x) (@lem3476496 _90228 t x)). Qed.
Lemma lem3476500 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term32 _90228 x u t) = (term118 _90228 u t x).
Proof. exact (TRANS (@lem3476482 _90228 u x t) (@lem3476497 _90228 u t x)). Qed.
Lemma lem3476501 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term34 _90228 s x u t) = (term119 _90228 s u t x).
Proof. exact (MK_COMB (@lem3476478 _90228 s t) (@lem3476500 _90228 u t x)). Qed.
Lemma lem3476504 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term36 _90228 s x u) = (term120 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476501 _90228 s u t x)). Qed.
Lemma lem3476505 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476506 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term38 _90228 s x u) = (term121 _90228 s u x).
Proof. exact (MK_COMB (@lem3476505 _90228) (@lem3476504 _90228 s u x)). Qed.
Lemma lem3476511 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term112 _90228 x s u) = (term121 _90228 s u x).
Proof. exact (TRANS (@lem3476466 _90228 s x u) (@lem3476506 _90228 s u x)). Qed.
Lemma lem3476512 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : ((term84 _90228 x u s) = (term112 _90228 x s u)) = ((term99 _90228 u s x) = (term121 _90228 s u x)).
Proof. exact (MK_COMB (@lem3476444 _90228 u s x) (@lem3476511 _90228 s u x)). Qed.
Lemma lem3476515 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term122 _90228 s u) = (term123 _90228 s u).
Proof. exact (fun_ext (fun x : _90228 => @lem3476512 _90228 s u x)). Qed.
Lemma lem3476516 {_90228 : Type'} : (@all _90228) = (@all _90228).
Proof. exact (eq_refl (@all _90228)). Qed.
Lemma lem3476517 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term69 _90228 s u) = (term124 _90228 s u).
Proof. exact (MK_COMB (@lem3476516 _90228) (@lem3476515 _90228 s u)). Qed.
Lemma lem3476522 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term70 _90228 s u) = (term125 _90228 s u).
Proof. exact (MK_COMB (@lem3476388 _90228 s) (@lem3476517 _90228 s u)). Qed.
Lemma lem3476525 {_90228 : Type'} (u : _90228 -> Prop) : (term71 _90228 u) = (term126 _90228 u).
Proof. exact (fun_ext (fun s : type686 _90228 => @lem3476522 _90228 s u)). Qed.
Lemma lem3476526 {_90228 : Type'} : (@all ((_90228 -> Prop) -> Prop)) = (@all ((_90228 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90228 -> Prop) -> Prop))). Qed.
Lemma lem3476527 {_90228 : Type'} (u : _90228 -> Prop) : (term72 _90228 u) = (term127 _90228 u).
Proof. exact (MK_COMB (@lem3476526 _90228) (@lem3476525 _90228 u)). Qed.
Lemma lem3476532 {_90228 : Type'} : (term73 _90228) = (term128 _90228).
Proof. exact (fun_ext (fun u : _90228 -> Prop => @lem3476527 _90228 u)). Qed.
Lemma lem3476533 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476534 {_90228 : Type'} : (term74 _90228) = (term129 _90228).
Proof. exact (MK_COMB (@lem3476533 _90228) (@lem3476532 _90228)). Qed.
Lemma lem3476539 {_90228 : Type'} : (term129 _90228) = (term74 _90228).
Proof. exact (SYM (@lem3476534 _90228)). Qed.
Lemma lem3476541 (p : Prop) : p = (term130 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3476542 {_90228 : Type'} : (term129 _90228) = (term131 _90228).
Proof. exact (@lem3476541 (term129 _90228)). Qed.
Lemma lem3476543 {_90228 : Type'} : (term131 _90228) = (term129 _90228).
Proof. exact (SYM (@lem3476542 _90228)). Qed.
Lemma lem3476544 {_90228 : Type'} (h1 : term132 _90228) : term132 _90228.
Proof. exact (h1). Qed.
Lemma lem3476547 {_90228 : Type'} (h1 : term131 _90228) : term131 _90228.
Proof. exact (h1). Qed.
Lemma lem3476548 {_90228 : Type'} : term133 _90228.
Proof. exact (fun h0 : term131 _90228 => @lem3476547 _90228 h0). Qed.
Lemma lem3476549 {_90228 : Type'} (h1 : term133 _90228) : term133 _90228.
Proof. exact (h1). Qed.
Lemma lem3476550 {_90228 : Type'} (h1 : term131 _90228) : term131 _90228.
Proof. exact (h1). Qed.
Lemma lem3476551 {_90228 : Type'} (h1 : term131 _90228) (h2 : term133 _90228) : term131 _90228.
Proof. exact (@lem3476549 _90228 h2 (@lem3476550 _90228 h1)). Qed.
Lemma lem3476552 {_90228 : Type'} (h1 : term131 _90228) : term134 _90228.
Proof. exact (fun h0 : term133 _90228 => @lem3476551 _90228 h1 h0). Qed.
Lemma lem3476553 {_90228 : Type'} (h1 : term133 _90228) : term133 _90228.
Proof. exact (h1). Qed.
Lemma lem3476554 {_90228 : Type'} (h1 : term131 _90228) (h2 : term133 _90228) : term131 _90228.
Proof. exact (@lem3476552 _90228 h1 (@lem3476553 _90228 h2)). Qed.
Lemma lem3476555 {_90228 : Type'} (h1 : term133 _90228) : term133 _90228.
Proof. exact (fun h0 : term131 _90228 => @lem3476554 _90228 h0 h1). Qed.
Lemma lem3476556 {_90228 : Type'} : term135 _90228.
Proof. exact (fun h0 : term133 _90228 => @lem3476555 _90228 h0). Qed.
Lemma lem3476559 {_90228 : Type'} : term133 _90228.
Proof. exact (@lem3476556 _90228 (@lem3476548 _90228)). Qed.
Lemma lem3476560 {_90228 : Type'} : term133 _90228.
Proof. exact (@lem3476559 _90228). Qed.
Lemma lem3476562 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3476563 {_90228 : Type'} : (term131 _90228) = (term136 _90228).
Proof. exact (@lem3476562 (term132 _90228)). Qed.
Lemma lem3476565 (t : Prop) : (term137 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3476566 {_90228 : Type'} : (term136 _90228) = (term129 _90228).
Proof. exact (@lem3476565 (term129 _90228)). Qed.
Lemma lem3476629 {_90228 : Type'} : (term131 _90228) = (term129 _90228).
Proof. exact (TRANS (@lem3476563 _90228) (@lem3476566 _90228)). Qed.
Lemma lem3476640 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term119 _90228 s u t x) = (term119 _90228 s u t x).
Proof. exact (eq_refl (term119 _90228 s u t x)). Qed.
Lemma lem3476641 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term120 _90228 s u x) = (term120 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476640 _90228 s u t x)). Qed.
Lemma lem3476642 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476643 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term121 _90228 s u x) = (term121 _90228 s u x).
Proof. exact (MK_COMB (@lem3476642 _90228) (@lem3476641 _90228 s u x)). Qed.
Lemma lem3476648 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term93 _90228 s t x) = (term93 _90228 s t x).
Proof. exact (eq_refl (term93 _90228 s t x)). Qed.
Lemma lem3476649 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term95 _90228 s x) = (term95 _90228 s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476648 _90228 s t x)). Qed.
Lemma lem3476650 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3476651 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term96 _90228 s x) = (term96 _90228 s x).
Proof. exact (MK_COMB (@lem3476650 _90228) (@lem3476649 _90228 s x)). Qed.
Lemma lem3476652 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476653 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term98 _90228 s x) = (term98 _90228 s x).
Proof. exact (MK_COMB (@lem3476652) (@lem3476651 _90228 s x)). Qed.
Lemma lem3476656 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term87 _90228 u x) = (term87 _90228 u x).
Proof. exact (eq_refl (term87 _90228 u x)). Qed.
Lemma lem3476657 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term99 _90228 u s x) = (term99 _90228 u s x).
Proof. exact (MK_COMB (@lem3476656 _90228 u x) (@lem3476653 _90228 s x)). Qed.
Lemma lem3476658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3476659 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term101 _90228 u s x) = (term101 _90228 u s x).
Proof. exact (MK_COMB (@lem3476658) (@lem3476657 _90228 u s x)). Qed.
Lemma lem3476660 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : ((term99 _90228 u s x) = (term121 _90228 s u x)) = ((term99 _90228 u s x) = (term121 _90228 s u x)).
Proof. exact (MK_COMB (@lem3476659 _90228 u s x) (@lem3476643 _90228 s u x)). Qed.
Lemma lem3476661 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term123 _90228 s u) = (term123 _90228 s u).
Proof. exact (fun_ext (fun x : _90228 => @lem3476660 _90228 s u x)). Qed.
Lemma lem3476662 {_90228 : Type'} : (@all _90228) = (@all _90228).
Proof. exact (eq_refl (@all _90228)). Qed.
Lemma lem3476663 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term124 _90228 s u) = (term124 _90228 s u).
Proof. exact (MK_COMB (@lem3476662 _90228) (@lem3476661 _90228 s u)). Qed.
Lemma lem3476666 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : (term77 _90228 s x) = (term77 _90228 s x).
Proof. exact (eq_refl (term77 _90228 s x)). Qed.
Lemma lem3476667 {_90228 : Type'} (s : type686 _90228) : (term79 _90228 s) = (term79 _90228 s).
Proof. exact (fun_ext (fun x : _90228 -> Prop => @lem3476666 _90228 s x)). Qed.
Lemma lem3476668 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476669 {_90228 : Type'} (s : type686 _90228) : (term80 _90228 s) = (term80 _90228 s).
Proof. exact (MK_COMB (@lem3476668 _90228) (@lem3476667 _90228 s)). Qed.
Lemma lem3476670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476671 {_90228 : Type'} (s : type686 _90228) : (term81 _90228 s) = (term81 _90228 s).
Proof. exact (MK_COMB (@lem3476670) (@lem3476669 _90228 s)). Qed.
Lemma lem3476672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3476673 {_90228 : Type'} (s : type686 _90228) : (term82 _90228 s) = (term82 _90228 s).
Proof. exact (MK_COMB (@lem3476672) (@lem3476671 _90228 s)). Qed.
Lemma lem3476674 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : (term125 _90228 s u) = (term125 _90228 s u).
Proof. exact (MK_COMB (@lem3476673 _90228 s) (@lem3476663 _90228 s u)). Qed.
Lemma lem3476675 {_90228 : Type'} (u : _90228 -> Prop) : (term126 _90228 u) = (term126 _90228 u).
Proof. exact (fun_ext (fun s : type686 _90228 => @lem3476674 _90228 s u)). Qed.
Lemma lem3476676 {_90228 : Type'} : (@all ((_90228 -> Prop) -> Prop)) = (@all ((_90228 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90228 -> Prop) -> Prop))). Qed.
Lemma lem3476677 {_90228 : Type'} (u : _90228 -> Prop) : (term127 _90228 u) = (term127 _90228 u).
Proof. exact (MK_COMB (@lem3476676 _90228) (@lem3476675 _90228 u)). Qed.
Lemma lem3476678 {_90228 : Type'} : (term128 _90228) = (term128 _90228).
Proof. exact (fun_ext (fun u : _90228 -> Prop => @lem3476677 _90228 u)). Qed.
Lemma lem3476679 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476680 {_90228 : Type'} : (term129 _90228) = (term129 _90228).
Proof. exact (MK_COMB (@lem3476679 _90228) (@lem3476678 _90228)). Qed.
Lemma lem3476729 {_90228 : Type'} : (term131 _90228) = (term129 _90228).
Proof. exact (TRANS (@lem3476629 _90228) (@lem3476680 _90228)). Qed.
Lemma lem3476730 {_90228 : Type'} : (term129 _90228) = (term131 _90228).
Proof. exact (SYM (@lem3476729 _90228)). Qed.
Lemma lem3476731 {_90228 : Type'} (s : type686 _90228) (h1 : term81 _90228 s) : term81 _90228 s.
Proof. exact (h1). Qed.
Lemma lem3476733 (p : Prop) : p = (term130 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3476734 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : ((term99 _90228 u s x) = (term121 _90228 s u x)) = (term138 _90228 s u x).
Proof. exact (@lem3476733 ((term99 _90228 u s x) = (term121 _90228 s u x))). Qed.
Lemma lem3476735 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term138 _90228 s u x) = ((term99 _90228 u s x) = (term121 _90228 s u x)).
Proof. exact (SYM (@lem3476734 _90228 s u x)). Qed.
Lemma lem3476736 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term139 _90228 s u x) : term139 _90228 s u x.
Proof. exact (h1). Qed.
Lemma lem3476739 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : (term140 _90228 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3476740 {_90228 : Type'} (P : type686 _90228) : (term141 _90228 P) = (term142 _90228 P).
Proof. exact (@lem18392 (_90228 -> Prop) P). Qed.
Lemma lem3476741 {_90228 : Type'} (s : type686 _90228) : (term81 _90228 s) = (term143 _90228 s).
Proof. exact (@lem3476740 _90228 (term79 _90228 s)). Qed.
Lemma lem3476742 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : (term144 _90228 s x) = (term77 _90228 s x).
Proof. exact (eq_refl (term144 _90228 s x)). Qed.
Lemma lem3476743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476744 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : (term145 _90228 s x) = (term140 _90228 s x).
Proof. exact (MK_COMB (@lem3476743) (@lem3476742 _90228 s x)). Qed.
Lemma lem3476745 {_90228 : Type'} (s : type686 _90228) (x : _90228 -> Prop) : (term145 _90228 s x) = (s x).
Proof. exact (TRANS (@lem3476744 _90228 s x) (@lem3476739 _90228 s x)). Qed.
Lemma lem3476746 {_90228 : Type'} (s : type686 _90228) : (term146 _90228 s) = (term147 _90228 s).
Proof. exact (fun_ext (fun x : _90228 -> Prop => @lem3476745 _90228 s x)). Qed.
Lemma lem3476747 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3476748 {_90228 : Type'} (s : type686 _90228) : (term143 _90228 s) = (term148 _90228 s).
Proof. exact (MK_COMB (@lem3476747 _90228) (@lem3476746 _90228 s)). Qed.
Lemma lem3476757 {_90228 : Type'} (s : type686 _90228) : (term81 _90228 s) = (term148 _90228 s).
Proof. exact (TRANS (@lem3476741 _90228 s) (@lem3476748 _90228 s)). Qed.
Lemma lem3476758 {_90228 : Type'} (s : type686 _90228) (h1 : term81 _90228 s) : term148 _90228 s.
Proof. exact (EQ_MP (@lem3476757 _90228 s) (@lem3476731 _90228 s h1)). Qed.
Lemma lem3476769 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term149 _90228 s t x) = (term150 _90228 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3476772 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term93 _90228 s t x) = (term93 _90228 s t x).
Proof. exact (eq_refl (term93 _90228 s t x)). Qed.
Lemma lem3476773 {_90228 : Type'} (P : type686 _90228) : (term151 _90228 P) = (term80 _90228 P).
Proof. exact (@lem18394 (_90228 -> Prop) P). Qed.
Lemma lem3476774 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term98 _90228 s x) = (term152 _90228 s x).
Proof. exact (@lem3476773 _90228 (term95 _90228 s x)). Qed.
Lemma lem3476775 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term153 _90228 s x t) = (term93 _90228 s t x).
Proof. exact (eq_refl (term153 _90228 s x t)). Qed.
Lemma lem3476776 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476777 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term154 _90228 s x t) = (term149 _90228 s t x).
Proof. exact (MK_COMB (@lem3476776) (@lem3476775 _90228 s t x)). Qed.
Lemma lem3476778 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term154 _90228 s x t) = (term150 _90228 s t x).
Proof. exact (TRANS (@lem3476777 _90228 s t x) (@lem3476769 _90228 s t x)). Qed.
Lemma lem3476779 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term155 _90228 s x) = (term156 _90228 s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476778 _90228 s t x)). Qed.
Lemma lem3476780 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476781 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term152 _90228 s x) = (term157 _90228 s x).
Proof. exact (MK_COMB (@lem3476780 _90228) (@lem3476779 _90228 s x)). Qed.
Lemma lem3476782 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term98 _90228 s x) = (term157 _90228 s x).
Proof. exact (TRANS (@lem3476774 _90228 s x) (@lem3476781 _90228 s x)). Qed.
Lemma lem3476783 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term95 _90228 s x) = (term95 _90228 s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476772 _90228 s t x)). Qed.
Lemma lem3476784 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3476785 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term96 _90228 s x) = (term96 _90228 s x).
Proof. exact (MK_COMB (@lem3476784 _90228) (@lem3476783 _90228 s x)). Qed.
Lemma lem3476786 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term158 _90228 s x) = (term96 _90228 s x).
Proof. exact (@lem16933 (term96 _90228 s x)). Qed.
Lemma lem3476787 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term158 _90228 s x) = (term96 _90228 s x).
Proof. exact (TRANS (@lem3476786 _90228 s x) (@lem3476785 _90228 s x)). Qed.
Lemma lem3476789 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term159 _90228 u x) = (term159 _90228 u x).
Proof. exact (eq_refl (term159 _90228 u x)). Qed.
Lemma lem3476790 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term160 _90228 u s x) = (term161 _90228 u s x).
Proof. exact (MK_COMB (@lem3476789 _90228 u x) (@lem3476787 _90228 s x)). Qed.
Lemma lem3476791 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term162 _90228 u s x) = (term160 _90228 u s x).
Proof. exact (@lem17045 (u x) (term98 _90228 s x)). Qed.
Lemma lem3476792 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term162 _90228 u s x) = (term161 _90228 u s x).
Proof. exact (TRANS (@lem3476791 _90228 u s x) (@lem3476790 _90228 u s x)). Qed.
Lemma lem3476794 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term87 _90228 u x) = (term87 _90228 u x).
Proof. exact (eq_refl (term87 _90228 u x)). Qed.
Lemma lem3476795 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term99 _90228 u s x) = (term163 _90228 u s x).
Proof. exact (MK_COMB (@lem3476794 _90228 u x) (@lem3476782 _90228 s x)). Qed.
Lemma lem3476803 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (term164 _90228 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3476805 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term159 _90228 u x) = (term159 _90228 u x).
Proof. exact (eq_refl (term159 _90228 u x)). Qed.
Lemma lem3476806 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term165 _90228 u t x) = (term166 _90228 u t x).
Proof. exact (MK_COMB (@lem3476805 _90228 u x) (@lem3476803 _90228 t x)). Qed.
Lemma lem3476807 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term167 _90228 u t x) = (term165 _90228 u t x).
Proof. exact (@lem17045 (u x) (term117 _90228 t x)). Qed.
Lemma lem3476808 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term167 _90228 u t x) = (term166 _90228 u t x).
Proof. exact (TRANS (@lem3476807 _90228 u t x) (@lem3476806 _90228 u t x)). Qed.
Lemma lem3476813 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term91 _90228 s t) = (term91 _90228 s t).
Proof. exact (eq_refl (term91 _90228 s t)). Qed.
Lemma lem3476814 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term168 _90228 s u t x) = (term169 _90228 s u t x).
Proof. exact (MK_COMB (@lem3476813 _90228 s t) (@lem3476808 _90228 u t x)). Qed.
Lemma lem3476815 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term170 _90228 s u t x) = (term168 _90228 s u t x).
Proof. exact (@lem17362 (s t) (term118 _90228 u t x)). Qed.
Lemma lem3476816 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term170 _90228 s u t x) = (term169 _90228 s u t x).
Proof. exact (TRANS (@lem3476815 _90228 s u t x) (@lem3476814 _90228 s u t x)). Qed.
Lemma lem3476821 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term119 _90228 s u t x) = (term171 _90228 s u t x).
Proof. exact (@lem17265 (s t) (term118 _90228 u t x)). Qed.
Lemma lem3476822 {_90228 : Type'} (P : type686 _90228) : (term141 _90228 P) = (term142 _90228 P).
Proof. exact (@lem18392 (_90228 -> Prop) P). Qed.
Lemma lem3476823 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term172 _90228 s u x) = (term173 _90228 s u x).
Proof. exact (@lem3476822 _90228 (term120 _90228 s u x)). Qed.
Lemma lem3476824 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term174 _90228 s u x t) = (term119 _90228 s u t x).
Proof. exact (eq_refl (term174 _90228 s u x t)). Qed.
Lemma lem3476825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3476826 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term175 _90228 s u x t) = (term170 _90228 s u t x).
Proof. exact (MK_COMB (@lem3476825) (@lem3476824 _90228 s u t x)). Qed.
Lemma lem3476827 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term175 _90228 s u x t) = (term169 _90228 s u t x).
Proof. exact (TRANS (@lem3476826 _90228 s u t x) (@lem3476816 _90228 s u t x)). Qed.
Lemma lem3476828 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term176 _90228 s u x) = (term177 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476827 _90228 s u t x)). Qed.
Lemma lem3476829 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3476830 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term173 _90228 s u x) = (term178 _90228 s u x).
Proof. exact (MK_COMB (@lem3476829 _90228) (@lem3476828 _90228 s u x)). Qed.
Lemma lem3476831 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term172 _90228 s u x) = (term178 _90228 s u x).
Proof. exact (TRANS (@lem3476823 _90228 s u x) (@lem3476830 _90228 s u x)). Qed.
Lemma lem3476832 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term120 _90228 s u x) = (term179 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3476821 _90228 s u t x)). Qed.
Lemma lem3476833 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3476834 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term121 _90228 s u x) = (term180 _90228 s u x).
Proof. exact (MK_COMB (@lem3476833 _90228) (@lem3476832 _90228 s u x)). Qed.
Lemma lem3476835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3476836 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term181 _90228 u s x) = (term182 _90228 u s x).
Proof. exact (MK_COMB (@lem3476835) (@lem3476792 _90228 u s x)). Qed.
Lemma lem3476837 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term183 _90228 s u x) = (term184 _90228 s u x).
Proof. exact (MK_COMB (@lem3476836 _90228 u s x) (@lem3476834 _90228 s u x)). Qed.
Lemma lem3476838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3476839 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term185 _90228 u s x) = (term186 _90228 u s x).
Proof. exact (MK_COMB (@lem3476838) (@lem3476795 _90228 u s x)). Qed.
Lemma lem3476840 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term187 _90228 s u x) = (term188 _90228 s u x).
Proof. exact (MK_COMB (@lem3476839 _90228 u s x) (@lem3476831 _90228 s u x)). Qed.
Lemma lem3476841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3476842 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term189 _90228 s u x) = (term190 _90228 s u x).
Proof. exact (MK_COMB (@lem3476841) (@lem3476840 _90228 s u x)). Qed.
Lemma lem3476843 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term191 _90228 s u x) = (term192 _90228 s u x).
Proof. exact (MK_COMB (@lem3476842 _90228 s u x) (@lem3476837 _90228 s u x)). Qed.
Lemma lem3476844 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term139 _90228 s u x) = (term191 _90228 s u x).
Proof. exact (@lem17646 (term99 _90228 u s x) (term121 _90228 s u x)). Qed.
Lemma lem3476845 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term139 _90228 s u x) = (term192 _90228 s u x).
Proof. exact (TRANS (@lem3476844 _90228 s u x) (@lem3476843 _90228 s u x)). Qed.
Lemma lem3477000 {A : Type'} (P : Prop) (Q : A -> Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3477001 {_90228 : Type'} (P : Prop) (Q : type686 _90228) : (term195 _90228 P Q) = (term196 _90228 P Q).
Proof. exact (@lem3477000 (_90228 -> Prop) P Q). Qed.
Lemma lem3477002 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term197 _90228 s u x) = (term198 _90228 s u x).
Proof. exact (@lem3477001 _90228 (term163 _90228 u s x) (term177 _90228 s u x)). Qed.
Lemma lem3477003 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term199 _90228 s u x t) = (term169 _90228 s u t x).
Proof. exact (eq_refl (term199 _90228 s u x t)). Qed.
Lemma lem3477004 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term200 _90228 s u x) = (term177 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477003 _90228 s u t x)). Qed.
Lemma lem3477005 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477006 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term201 _90228 s u x) = (term178 _90228 s u x).
Proof. exact (MK_COMB (@lem3477005 _90228) (@lem3477004 _90228 s u x)). Qed.
Lemma lem3477007 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term186 _90228 u s x) = (term186 _90228 u s x).
Proof. exact (eq_refl (term186 _90228 u s x)). Qed.
Lemma lem3477008 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term197 _90228 s u x) = (term188 _90228 s u x).
Proof. exact (MK_COMB (@lem3477007 _90228 u s x) (@lem3477006 _90228 s u x)). Qed.
Lemma lem3477009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3477010 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term202 _90228 s u x) = (term203 _90228 s u x).
Proof. exact (MK_COMB (@lem3477009) (@lem3477008 _90228 s u x)). Qed.
Lemma lem3477011 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term199 _90228 s u x t) = (term169 _90228 s u t x).
Proof. exact (eq_refl (term199 _90228 s u x t)). Qed.
Lemma lem3477012 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term186 _90228 u s x) = (term186 _90228 u s x).
Proof. exact (eq_refl (term186 _90228 u s x)). Qed.
Lemma lem3477013 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term204 _90228 s u x t) = (term205 _90228 s u t x).
Proof. exact (MK_COMB (@lem3477012 _90228 u s x) (@lem3477011 _90228 s u t x)). Qed.
Lemma lem3477014 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term206 _90228 s u x) = (term207 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477013 _90228 s u t x)). Qed.
Lemma lem3477015 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477016 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term198 _90228 s u x) = (term208 _90228 s u x).
Proof. exact (MK_COMB (@lem3477015 _90228) (@lem3477014 _90228 s u x)). Qed.
Lemma lem3477017 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : ((term197 _90228 s u x) = (term198 _90228 s u x)) = ((term188 _90228 s u x) = (term208 _90228 s u x)).
Proof. exact (MK_COMB (@lem3477010 _90228 s u x) (@lem3477016 _90228 s u x)). Qed.
Lemma lem3477018 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term188 _90228 s u x) = (term208 _90228 s u x).
Proof. exact (EQ_MP (@lem3477017 _90228 s u x) (@lem3477002 _90228 s u x)). Qed.
Lemma lem3477019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477020 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term190 _90228 s u x) = (term209 _90228 s u x).
Proof. exact (MK_COMB (@lem3477019) (@lem3477018 _90228 s u x)). Qed.
Lemma lem3477022 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3477023 {_90228 : Type'} (P : Prop) (Q : type686 _90228) : (term212 _90228 P Q) = (term213 _90228 P Q).
Proof. exact (@lem3477022 (_90228 -> Prop) P Q). Qed.
Lemma lem3477024 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term214 _90228 u s x) = (term215 _90228 u s x).
Proof. exact (@lem3477023 _90228 (term117 _90228 u x) (term95 _90228 s x)). Qed.
Lemma lem3477025 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term153 _90228 s x t) = (term93 _90228 s t x).
Proof. exact (eq_refl (term153 _90228 s x t)). Qed.
Lemma lem3477026 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term216 _90228 s x) = (term95 _90228 s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477025 _90228 s t x)). Qed.
Lemma lem3477027 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477028 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term217 _90228 s x) = (term96 _90228 s x).
Proof. exact (MK_COMB (@lem3477027 _90228) (@lem3477026 _90228 s x)). Qed.
Lemma lem3477029 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term159 _90228 u x) = (term159 _90228 u x).
Proof. exact (eq_refl (term159 _90228 u x)). Qed.
Lemma lem3477030 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term214 _90228 u s x) = (term161 _90228 u s x).
Proof. exact (MK_COMB (@lem3477029 _90228 u x) (@lem3477028 _90228 s x)). Qed.
Lemma lem3477031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3477032 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term218 _90228 u s x) = (term219 _90228 u s x).
Proof. exact (MK_COMB (@lem3477031) (@lem3477030 _90228 u s x)). Qed.
Lemma lem3477033 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term153 _90228 s x t) = (term93 _90228 s t x).
Proof. exact (eq_refl (term153 _90228 s x t)). Qed.
Lemma lem3477034 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term159 _90228 u x) = (term159 _90228 u x).
Proof. exact (eq_refl (term159 _90228 u x)). Qed.
Lemma lem3477035 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term220 _90228 u s x t) = (term221 _90228 u s t x).
Proof. exact (MK_COMB (@lem3477034 _90228 u x) (@lem3477033 _90228 s t x)). Qed.
Lemma lem3477036 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term222 _90228 u s x) = (term223 _90228 u s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477035 _90228 u s t x)). Qed.
Lemma lem3477037 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477038 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term215 _90228 u s x) = (term224 _90228 u s x).
Proof. exact (MK_COMB (@lem3477037 _90228) (@lem3477036 _90228 u s x)). Qed.
Lemma lem3477039 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : ((term214 _90228 u s x) = (term215 _90228 u s x)) = ((term161 _90228 u s x) = (term224 _90228 u s x)).
Proof. exact (MK_COMB (@lem3477032 _90228 u s x) (@lem3477038 _90228 u s x)). Qed.
Lemma lem3477040 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term161 _90228 u s x) = (term224 _90228 u s x).
Proof. exact (EQ_MP (@lem3477039 _90228 u s x) (@lem3477024 _90228 u s x)). Qed.
Lemma lem3477041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477042 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term182 _90228 u s x) = (term225 _90228 u s x).
Proof. exact (MK_COMB (@lem3477041) (@lem3477040 _90228 u s x)). Qed.
Lemma lem3477043 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term180 _90228 s u x) = (term180 _90228 s u x).
Proof. exact (eq_refl (term180 _90228 s u x)). Qed.
Lemma lem3477044 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term184 _90228 s u x) = (term226 _90228 s u x).
Proof. exact (MK_COMB (@lem3477042 _90228 u s x) (@lem3477043 _90228 s u x)). Qed.
Lemma lem3477046 {A : Type'} (P : A -> Prop) (Q : Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3477047 {_90228 : Type'} (P : type686 _90228) (Q : Prop) : (term229 _90228 P Q) = (term230 _90228 P Q).
Proof. exact (@lem3477046 (_90228 -> Prop) P Q). Qed.
Lemma lem3477048 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term231 _90228 s u x) = (term232 _90228 s u x).
Proof. exact (@lem3477047 _90228 (term223 _90228 u s x) (term180 _90228 s u x)). Qed.
Lemma lem3477049 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term233 _90228 u s x t) = (term221 _90228 u s t x).
Proof. exact (eq_refl (term233 _90228 u s x t)). Qed.
Lemma lem3477050 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term234 _90228 u s x) = (term223 _90228 u s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477049 _90228 u s t x)). Qed.
Lemma lem3477051 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477052 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term235 _90228 u s x) = (term224 _90228 u s x).
Proof. exact (MK_COMB (@lem3477051 _90228) (@lem3477050 _90228 u s x)). Qed.
Lemma lem3477053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477054 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term236 _90228 u s x) = (term225 _90228 u s x).
Proof. exact (MK_COMB (@lem3477053) (@lem3477052 _90228 u s x)). Qed.
Lemma lem3477055 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term180 _90228 s u x) = (term180 _90228 s u x).
Proof. exact (eq_refl (term180 _90228 s u x)). Qed.
Lemma lem3477056 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term231 _90228 s u x) = (term226 _90228 s u x).
Proof. exact (MK_COMB (@lem3477054 _90228 u s x) (@lem3477055 _90228 s u x)). Qed.
Lemma lem3477057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3477058 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term237 _90228 s u x) = (term238 _90228 s u x).
Proof. exact (MK_COMB (@lem3477057) (@lem3477056 _90228 s u x)). Qed.
Lemma lem3477059 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term233 _90228 u s x t) = (term221 _90228 u s t x).
Proof. exact (eq_refl (term233 _90228 u s x t)). Qed.
Lemma lem3477060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477061 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term239 _90228 u s x t) = (term240 _90228 u s t x).
Proof. exact (MK_COMB (@lem3477060) (@lem3477059 _90228 u s t x)). Qed.
Lemma lem3477062 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term180 _90228 s u x) = (term180 _90228 s u x).
Proof. exact (eq_refl (term180 _90228 s u x)). Qed.
Lemma lem3477063 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term241 _90228 t s u x) = (term242 _90228 t s u x).
Proof. exact (MK_COMB (@lem3477061 _90228 u s t x) (@lem3477062 _90228 s u x)). Qed.
Lemma lem3477064 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term243 _90228 s u x) = (term244 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477063 _90228 t s u x)). Qed.
Lemma lem3477065 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477066 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term232 _90228 s u x) = (term245 _90228 s u x).
Proof. exact (MK_COMB (@lem3477065 _90228) (@lem3477064 _90228 s u x)). Qed.
Lemma lem3477067 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : ((term231 _90228 s u x) = (term232 _90228 s u x)) = ((term226 _90228 s u x) = (term245 _90228 s u x)).
Proof. exact (MK_COMB (@lem3477058 _90228 s u x) (@lem3477066 _90228 s u x)). Qed.
Lemma lem3477068 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term226 _90228 s u x) = (term245 _90228 s u x).
Proof. exact (EQ_MP (@lem3477067 _90228 s u x) (@lem3477048 _90228 s u x)). Qed.
Lemma lem3477069 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term184 _90228 s u x) = (term245 _90228 s u x).
Proof. exact (TRANS (@lem3477044 _90228 s u x) (@lem3477068 _90228 s u x)). Qed.
Lemma lem3477070 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term192 _90228 s u x) = (term246 _90228 s u x).
Proof. exact (MK_COMB (@lem3477020 _90228 s u x) (@lem3477069 _90228 s u x)). Qed.
Lemma lem3477072 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3477073 {_90228 : Type'} (P : type686 _90228) (Q : type686 _90228) : (term249 _90228 P Q) = (term250 _90228 P Q).
Proof. exact (@lem3477072 (_90228 -> Prop) P Q). Qed.
Lemma lem3477074 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term251 _90228 s u x) = (term252 _90228 s u x).
Proof. exact (@lem3477073 _90228 (term207 _90228 s u x) (term244 _90228 s u x)). Qed.
Lemma lem3477075 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term253 _90228 s u x t) = (term205 _90228 s u t x).
Proof. exact (eq_refl (term253 _90228 s u x t)). Qed.
Lemma lem3477076 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term254 _90228 s u x) = (term207 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477075 _90228 s u t x)). Qed.
Lemma lem3477077 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477078 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term255 _90228 s u x) = (term208 _90228 s u x).
Proof. exact (MK_COMB (@lem3477077 _90228) (@lem3477076 _90228 s u x)). Qed.
Lemma lem3477079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477080 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term256 _90228 s u x) = (term209 _90228 s u x).
Proof. exact (MK_COMB (@lem3477079) (@lem3477078 _90228 s u x)). Qed.
Lemma lem3477081 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term257 _90228 s u x t) = (term242 _90228 t s u x).
Proof. exact (eq_refl (term257 _90228 s u x t)). Qed.
Lemma lem3477082 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term258 _90228 s u x) = (term244 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477081 _90228 t s u x)). Qed.
Lemma lem3477083 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477084 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term259 _90228 s u x) = (term245 _90228 s u x).
Proof. exact (MK_COMB (@lem3477083 _90228) (@lem3477082 _90228 s u x)). Qed.
Lemma lem3477085 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term251 _90228 s u x) = (term246 _90228 s u x).
Proof. exact (MK_COMB (@lem3477080 _90228 s u x) (@lem3477084 _90228 s u x)). Qed.
Lemma lem3477086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3477087 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term260 _90228 s u x) = (term261 _90228 s u x).
Proof. exact (MK_COMB (@lem3477086) (@lem3477085 _90228 s u x)). Qed.
Lemma lem3477088 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term253 _90228 s u x t) = (term205 _90228 s u t x).
Proof. exact (eq_refl (term253 _90228 s u x t)). Qed.
Lemma lem3477089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477090 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term262 _90228 s u x t) = (term263 _90228 s u t x).
Proof. exact (MK_COMB (@lem3477089) (@lem3477088 _90228 s u t x)). Qed.
Lemma lem3477091 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term257 _90228 s u x t) = (term242 _90228 t s u x).
Proof. exact (eq_refl (term257 _90228 s u x t)). Qed.
Lemma lem3477092 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term264 _90228 s u x t) = (term265 _90228 t s u x).
Proof. exact (MK_COMB (@lem3477090 _90228 s u t x) (@lem3477091 _90228 t s u x)). Qed.
Lemma lem3477093 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term266 _90228 s u x) = (term267 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477092 _90228 t s u x)). Qed.
Lemma lem3477094 {_90228 : Type'} : (@ex (_90228 -> Prop)) = (@ex (_90228 -> Prop)).
Proof. exact (eq_refl (@ex (_90228 -> Prop))). Qed.
Lemma lem3477095 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term252 _90228 s u x) = (term268 _90228 s u x).
Proof. exact (MK_COMB (@lem3477094 _90228) (@lem3477093 _90228 s u x)). Qed.
Lemma lem3477096 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : ((term251 _90228 s u x) = (term252 _90228 s u x)) = ((term246 _90228 s u x) = (term268 _90228 s u x)).
Proof. exact (MK_COMB (@lem3477087 _90228 s u x) (@lem3477095 _90228 s u x)). Qed.
Lemma lem3477097 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term246 _90228 s u x) = (term268 _90228 s u x).
Proof. exact (EQ_MP (@lem3477096 _90228 s u x) (@lem3477074 _90228 s u x)). Qed.
Lemma lem3477099 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term192 _90228 s u x) = (term268 _90228 s u x).
Proof. exact (TRANS (@lem3477070 _90228 s u x) (@lem3477097 _90228 s u x)). Qed.
Lemma lem3477100 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term139 _90228 s u x) = (term268 _90228 s u x).
Proof. exact (TRANS (@lem3476845 _90228 s u x) (@lem3477099 _90228 s u x)). Qed.
Lemma lem3477101 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term139 _90228 s u x) : term268 _90228 s u x.
Proof. exact (EQ_MP (@lem3477100 _90228 s u x) (@lem3476736 _90228 s u x h1)). Qed.
Lemma lem3477102 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term265 _90228 t s u x) : term265 _90228 t s u x.
Proof. exact (h1). Qed.
Lemma lem3477103 {_90228 : Type'} (s : type686 _90228) (x' : _90228 -> Prop) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3477104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3477109 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477110 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477109 _90228 Prop f x). Qed.
Lemma lem3477112 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (t x) = (@I (_90228 -> Prop) t x).
Proof. exact (@lem3477110 _90228 t x). Qed.
Lemma lem3477113 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (term117 _90228 t x) = (term269 _90228 t x).
Proof. exact (MK_COMB (@lem3477104) (@lem3477112 _90228 t x)). Qed.
Lemma lem3477118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477119 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477118 _90228 Prop f x). Qed.
Lemma lem3477121 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (u x) = (@I (_90228 -> Prop) u x).
Proof. exact (@lem3477119 _90228 u x). Qed.
Lemma lem3477122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477123 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term87 _90228 u x) = (term270 _90228 u x).
Proof. exact (MK_COMB (@lem3477122) (@lem3477121 _90228 u x)). Qed.
Lemma lem3477124 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term118 _90228 u t x) = (term271 _90228 u t x).
Proof. exact (MK_COMB (@lem3477123 _90228 u x) (@lem3477113 _90228 t x)). Qed.
Lemma lem3477125 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3477130 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477131 {_90228 : Type'} (f : type686 _90228) (x : _90228 -> Prop) : (f x) = (@I ((_90228 -> Prop) -> Prop) f x).
Proof. exact (@lem3477130 (_90228 -> Prop) Prop f x). Qed.
Lemma lem3477133 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (s t) = (@I ((_90228 -> Prop) -> Prop) s t).
Proof. exact (@lem3477131 _90228 s t). Qed.
Lemma lem3477134 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term77 _90228 s t) = (term272 _90228 s t).
Proof. exact (MK_COMB (@lem3477125) (@lem3477133 _90228 s t)). Qed.
Lemma lem3477135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477136 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term273 _90228 s t) = (term274 _90228 s t).
Proof. exact (MK_COMB (@lem3477135) (@lem3477134 _90228 s t)). Qed.
Lemma lem3477137 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term171 _90228 s u t x) = (term275 _90228 s u t x).
Proof. exact (MK_COMB (@lem3477136 _90228 s t) (@lem3477124 _90228 u t x)). Qed.
Lemma lem3477138 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term179 _90228 s u x) = (term276 _90228 s u x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477137 _90228 s u t x)). Qed.
Lemma lem3477139 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3477140 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term180 _90228 s u x) = (term277 _90228 s u x).
Proof. exact (MK_COMB (@lem3477139 _90228) (@lem3477138 _90228 s u x)). Qed.
Lemma lem3477145 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477146 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477145 _90228 Prop f x). Qed.
Lemma lem3477148 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (t x) = (@I (_90228 -> Prop) t x).
Proof. exact (@lem3477146 _90228 t x). Qed.
Lemma lem3477153 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477154 {_90228 : Type'} (f : type686 _90228) (x : _90228 -> Prop) : (f x) = (@I ((_90228 -> Prop) -> Prop) f x).
Proof. exact (@lem3477153 (_90228 -> Prop) Prop f x). Qed.
Lemma lem3477156 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (s t) = (@I ((_90228 -> Prop) -> Prop) s t).
Proof. exact (@lem3477154 _90228 s t). Qed.
Lemma lem3477157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477158 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term91 _90228 s t) = (term278 _90228 s t).
Proof. exact (MK_COMB (@lem3477157) (@lem3477156 _90228 s t)). Qed.
Lemma lem3477159 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term93 _90228 s t x) = (term279 _90228 s t x).
Proof. exact (MK_COMB (@lem3477158 _90228 s t) (@lem3477148 _90228 t x)). Qed.
Lemma lem3477160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3477165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477166 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477165 _90228 Prop f x). Qed.
Lemma lem3477168 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (u x) = (@I (_90228 -> Prop) u x).
Proof. exact (@lem3477166 _90228 u x). Qed.
Lemma lem3477169 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term117 _90228 u x) = (term269 _90228 u x).
Proof. exact (MK_COMB (@lem3477160) (@lem3477168 _90228 u x)). Qed.
Lemma lem3477170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477171 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term159 _90228 u x) = (term280 _90228 u x).
Proof. exact (MK_COMB (@lem3477170) (@lem3477169 _90228 u x)). Qed.
Lemma lem3477172 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term221 _90228 u s t x) = (term281 _90228 u s t x).
Proof. exact (MK_COMB (@lem3477171 _90228 u x) (@lem3477159 _90228 s t x)). Qed.
Lemma lem3477173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477174 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term240 _90228 u s t x) = (term282 _90228 u s t x).
Proof. exact (MK_COMB (@lem3477173) (@lem3477172 _90228 u s t x)). Qed.
Lemma lem3477175 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term242 _90228 t s u x) = (term283 _90228 t s u x).
Proof. exact (MK_COMB (@lem3477174 _90228 u s t x) (@lem3477140 _90228 s u x)). Qed.
Lemma lem3477180 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477181 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477180 _90228 Prop f x). Qed.
Lemma lem3477183 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (t x) = (@I (_90228 -> Prop) t x).
Proof. exact (@lem3477181 _90228 t x). Qed.
Lemma lem3477184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3477189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477190 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477189 _90228 Prop f x). Qed.
Lemma lem3477192 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (u x) = (@I (_90228 -> Prop) u x).
Proof. exact (@lem3477190 _90228 u x). Qed.
Lemma lem3477193 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term117 _90228 u x) = (term269 _90228 u x).
Proof. exact (MK_COMB (@lem3477184) (@lem3477192 _90228 u x)). Qed.
Lemma lem3477194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477195 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term159 _90228 u x) = (term280 _90228 u x).
Proof. exact (MK_COMB (@lem3477194) (@lem3477193 _90228 u x)). Qed.
Lemma lem3477196 {_90228 : Type'} (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term166 _90228 u t x) = (term284 _90228 u t x).
Proof. exact (MK_COMB (@lem3477195 _90228 u x) (@lem3477183 _90228 t x)). Qed.
Lemma lem3477201 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477202 {_90228 : Type'} (f : type686 _90228) (x : _90228 -> Prop) : (f x) = (@I ((_90228 -> Prop) -> Prop) f x).
Proof. exact (@lem3477201 (_90228 -> Prop) Prop f x). Qed.
Lemma lem3477204 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (s t) = (@I ((_90228 -> Prop) -> Prop) s t).
Proof. exact (@lem3477202 _90228 s t). Qed.
Lemma lem3477205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477206 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term91 _90228 s t) = (term278 _90228 s t).
Proof. exact (MK_COMB (@lem3477205) (@lem3477204 _90228 s t)). Qed.
Lemma lem3477207 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term169 _90228 s u t x) = (term285 _90228 s u t x).
Proof. exact (MK_COMB (@lem3477206 _90228 s t) (@lem3477196 _90228 u t x)). Qed.
Lemma lem3477208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3477213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477214 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477213 _90228 Prop f x). Qed.
Lemma lem3477216 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (t x) = (@I (_90228 -> Prop) t x).
Proof. exact (@lem3477214 _90228 t x). Qed.
Lemma lem3477217 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (term117 _90228 t x) = (term269 _90228 t x).
Proof. exact (MK_COMB (@lem3477208) (@lem3477216 _90228 t x)). Qed.
Lemma lem3477218 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3477223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477224 {_90228 : Type'} (f : type686 _90228) (x : _90228 -> Prop) : (f x) = (@I ((_90228 -> Prop) -> Prop) f x).
Proof. exact (@lem3477223 (_90228 -> Prop) Prop f x). Qed.
Lemma lem3477226 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (s t) = (@I ((_90228 -> Prop) -> Prop) s t).
Proof. exact (@lem3477224 _90228 s t). Qed.
Lemma lem3477227 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term77 _90228 s t) = (term272 _90228 s t).
Proof. exact (MK_COMB (@lem3477218) (@lem3477226 _90228 s t)). Qed.
Lemma lem3477228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477229 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term273 _90228 s t) = (term274 _90228 s t).
Proof. exact (MK_COMB (@lem3477228) (@lem3477227 _90228 s t)). Qed.
Lemma lem3477230 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term150 _90228 s t x) = (term286 _90228 s t x).
Proof. exact (MK_COMB (@lem3477229 _90228 s t) (@lem3477217 _90228 t x)). Qed.
Lemma lem3477231 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term156 _90228 s x) = (term287 _90228 s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477230 _90228 s t x)). Qed.
Lemma lem3477232 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3477233 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term157 _90228 s x) = (term288 _90228 s x).
Proof. exact (MK_COMB (@lem3477232 _90228) (@lem3477231 _90228 s x)). Qed.
Lemma lem3477238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477239 {_90228 : Type'} (f : _90228 -> Prop) (x : _90228) : (f x) = (@I (_90228 -> Prop) f x).
Proof. exact (@lem3477238 _90228 Prop f x). Qed.
Lemma lem3477241 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (u x) = (@I (_90228 -> Prop) u x).
Proof. exact (@lem3477239 _90228 u x). Qed.
Lemma lem3477242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477243 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term87 _90228 u x) = (term270 _90228 u x).
Proof. exact (MK_COMB (@lem3477242) (@lem3477241 _90228 u x)). Qed.
Lemma lem3477244 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term163 _90228 u s x) = (term289 _90228 u s x).
Proof. exact (MK_COMB (@lem3477243 _90228 u x) (@lem3477233 _90228 s x)). Qed.
Lemma lem3477245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3477246 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term186 _90228 u s x) = (term290 _90228 u s x).
Proof. exact (MK_COMB (@lem3477245) (@lem3477244 _90228 u s x)). Qed.
Lemma lem3477247 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term205 _90228 s u t x) = (term291 _90228 s u t x).
Proof. exact (MK_COMB (@lem3477246 _90228 u s x) (@lem3477207 _90228 s u t x)). Qed.
Lemma lem3477248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3477249 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) : (term263 _90228 s u t x) = (term292 _90228 s u t x).
Proof. exact (MK_COMB (@lem3477248) (@lem3477247 _90228 s u t x)). Qed.
Lemma lem3477250 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) : (term265 _90228 t s u x) = (term293 _90228 t s u x).
Proof. exact (MK_COMB (@lem3477249 _90228 s u t x) (@lem3477175 _90228 t s u x)). Qed.
Lemma lem3477251 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term265 _90228 t s u x) : term293 _90228 t s u x.
Proof. exact (EQ_MP (@lem3477250 _90228 t s u x) (@lem3477102 _90228 t s u x h1)). Qed.
Lemma lem3477256 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3477257 {_90228 : Type'} (f : type686 _90228) (x : _90228 -> Prop) : (f x) = (@I ((_90228 -> Prop) -> Prop) f x).
Proof. exact (@lem3477256 (_90228 -> Prop) Prop f x). Qed.
Lemma lem3477259 {_90228 : Type'} (s : type686 _90228) (x' : _90228 -> Prop) : (s x') = (@I ((_90228 -> Prop) -> Prop) s x').
Proof. exact (@lem3477257 _90228 s x'). Qed.
Lemma lem3477261 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term291 _90228 s u t x.
Proof. exact (h1). Qed.
Lemma lem3477262 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term283 _90228 t s u x.
Proof. exact (h1). Qed.
Lemma lem3477263 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term285 _90228 s u t x.
Proof. exact (proj2 (@lem3477261 _90228 s u t x h1)). Qed.
Lemma lem3477264 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term289 _90228 u s x.
Proof. exact (proj1 (@lem3477261 _90228 s u t x h1)). Qed.
Lemma lem3477265 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term284 _90228 u t x.
Proof. exact (proj2 (@lem3477263 _90228 s u t x h1)). Qed.
Lemma lem3477267 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term288 _90228 s x.
Proof. exact (proj2 (@lem3477264 _90228 s u t x h1)). Qed.
Lemma lem3477271 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term277 _90228 s u x.
Proof. exact (proj2 (@lem3477262 _90228 t s u x h1)). Qed.
Lemma lem3477272 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term281 _90228 u s t x.
Proof. exact (proj1 (@lem3477262 _90228 t s u x h1)). Qed.
Lemma lem3477274 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : term279 _90228 s t x.
Proof. exact (h1). Qed.
Lemma lem3477305 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) : term269 _90228 u x.
Proof. exact (h1). Qed.
Lemma lem3477325 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term286 _90228 s t x) = (term286 _90228 s t x).
Proof. exact (eq_refl (term286 _90228 s t x)). Qed.
Lemma lem3477326 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term287 _90228 s x) = (term287 _90228 s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477325 _90228 s t x)). Qed.
Lemma lem3477327 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3477329 {_90228 : Type'} (s : type686 _90228) (x : _90228) : (term288 _90228 s x) = (term288 _90228 s x).
Proof. exact (MK_COMB (@lem3477327 _90228) (@lem3477326 _90228 s x)). Qed.
Lemma lem3477330 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term288 _90228 s x.
Proof. exact (EQ_MP (@lem3477329 _90228 s x) (@lem3477267 _90228 s u t x h1)). Qed.
Lemma lem3477334 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) (h1 : @I (_90228 -> Prop) t x) : @I (_90228 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3477356 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term275 _90228 s u t x) = (term294 _90228 u s t x).
Proof. exact (@lem19490 (@I (_90228 -> Prop) u x) (term272 _90228 s t) (term269 _90228 t x)). Qed.
Lemma lem3477357 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term276 _90228 s u x) = (term295 _90228 u s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477356 _90228 u s t x)). Qed.
Lemma lem3477358 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3477360 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term277 _90228 s u x) = (term296 _90228 u s x).
Proof. exact (MK_COMB (@lem3477358 _90228) (@lem3477357 _90228 u s x)). Qed.
Lemma lem3477361 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term296 _90228 u s x.
Proof. exact (EQ_MP (@lem3477360 _90228 u s x) (@lem3477271 _90228 t s u x h1)). Qed.
Lemma lem3477365 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) : term269 _90228 u x.
Proof. exact (h1). Qed.
Lemma lem3477387 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) : (term275 _90228 s u t x) = (term294 _90228 u s t x).
Proof. exact (@lem19490 (@I (_90228 -> Prop) u x) (term272 _90228 s t) (term269 _90228 t x)). Qed.
Lemma lem3477388 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term276 _90228 s u x) = (term295 _90228 u s x).
Proof. exact (fun_ext (fun t : _90228 -> Prop => @lem3477387 _90228 u s t x)). Qed.
Lemma lem3477389 {_90228 : Type'} : (@all (_90228 -> Prop)) = (@all (_90228 -> Prop)).
Proof. exact (eq_refl (@all (_90228 -> Prop))). Qed.
Lemma lem3477391 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (x : _90228) : (term277 _90228 s u x) = (term296 _90228 u s x).
Proof. exact (MK_COMB (@lem3477389 _90228) (@lem3477388 _90228 u s x)). Qed.
Lemma lem3477392 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term296 _90228 u s x.
Proof. exact (EQ_MP (@lem3477391 _90228 u s x) (@lem3477271 _90228 t s u x h1)). Qed.
Lemma lem3477404 {_90228 : Type'} (_36683 : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term297 _90228 s x _36683.
Proof. exact (@lem3477330 _90228 s u t x h1 _36683). Qed.
Lemma lem3477405 {_90228 : Type'} (s : type686 _90228) (_36683 : _90228 -> Prop) (x : _90228) : (term297 _90228 s x _36683) = (term286 _90228 s _36683 x).
Proof. exact (eq_refl (term297 _90228 s x _36683)). Qed.
Lemma lem3477407 {_90228 : Type'} (_36684 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term298 _90228 u s x _36684.
Proof. exact (@lem3477361 _90228 t s u x h1 _36684). Qed.
Lemma lem3477408 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (_36684 : _90228 -> Prop) (x : _90228) : (term298 _90228 u s x _36684) = (term294 _90228 u s _36684 x).
Proof. exact (eq_refl (term298 _90228 u s x _36684)). Qed.
Lemma lem3477409 {_90228 : Type'} (_36684 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term294 _90228 u s _36684 x.
Proof. exact (EQ_MP (@lem3477408 _90228 u s _36684 x) (@lem3477407 _90228 _36684 t s u x h1)). Qed.
Lemma lem3477410 {_90228 : Type'} (_36685 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term298 _90228 u s x _36685.
Proof. exact (@lem3477392 _90228 t s u x h1 _36685). Qed.
Lemma lem3477411 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (_36685 : _90228 -> Prop) (x : _90228) : (term298 _90228 u s x _36685) = (term294 _90228 u s _36685 x).
Proof. exact (eq_refl (term298 _90228 u s x _36685)). Qed.
Lemma lem3477412 {_90228 : Type'} (_36685 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term294 _90228 u s _36685 x.
Proof. exact (EQ_MP (@lem3477411 _90228 u s _36685 x) (@lem3477410 _90228 _36685 t s u x h1)). Qed.
Lemma lem3477430 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) : term269 _90228 u x.
Proof. exact (h1). Qed.
Lemma lem3477442 {_90228 : Type'} (_36683 : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term286 _90228 s _36683 x.
Proof. exact (EQ_MP (@lem3477405 _90228 s _36683 x) (@lem3477404 _90228 _36683 s u t x h1)). Qed.
Lemma lem3477444 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) (h1 : @I (_90228 -> Prop) t x) : @I (_90228 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3477448 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) : term269 _90228 u x.
Proof. exact (h1). Qed.
Lemma lem3477454 {_90228 : Type'} (_36684 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term299 _90228 s _36684 u x.
Proof. exact (proj1 (@lem3477409 _90228 _36684 t s u x h1)). Qed.
Lemma lem3477478 {_90228 : Type'} (_36685 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term286 _90228 s _36685 x.
Proof. exact (proj2 (@lem3477412 _90228 _36685 t s u x h1)). Qed.
Lemma lem3477480 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : @I (_90228 -> Prop) u x.
Proof. exact (proj1 (@lem3477264 _90228 s u t x h1)). Qed.
Lemma lem3477481 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term300 _90228 u x.
Proof. exact (fun h0 : term269 _90228 u x => @lem3477480 _90228 s u t x h1). Qed.
Lemma lem3477483 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477484 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term300 _90228 u x) = (@I (_90228 -> Prop) u x).
Proof. exact (@lem3477483 (@I (_90228 -> Prop) u x)). Qed.
Lemma lem3477485 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : @I (_90228 -> Prop) u x.
Proof. exact (EQ_MP (@lem3477484 _90228 u x) (@lem3477481 _90228 s u t x h1)). Qed.
Lemma lem3477488 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3477490 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term269 _90228 u x) = (term302 _90228 u x).
Proof. exact (@lem3477488 (@I (_90228 -> Prop) u x)). Qed.
Lemma lem3477493 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) : term302 _90228 u x.
Proof. exact (EQ_MP (@lem3477490 _90228 u x) (@lem3477430 _90228 u x h1)). Qed.
Lemma lem3477496 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : False.
Proof. exact (@lem3477493 _90228 u x h1 (@lem3477485 _90228 s u t x h2)). Qed.
Lemma lem3477497 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : term303.
Proof. exact (fun h0 : ~ False => @lem3477496 _90228 s u t x h1 h2). Qed.
Lemma lem3477499 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477500 : term303 = False.
Proof. exact (@lem3477499 False). Qed.
Lemma lem3477501 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : False.
Proof. exact (EQ_MP (@lem3477500) (@lem3477497 _90228 s u t x h1 h2)). Qed.
Lemma lem3477503 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : @I ((_90228 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3477263 _90228 s u t x h1)). Qed.
Lemma lem3477504 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term304 _90228 s t.
Proof. exact (fun h0 : term272 _90228 s t => @lem3477503 _90228 s u t x h1). Qed.
Lemma lem3477506 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477507 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term304 _90228 s t) = (@I ((_90228 -> Prop) -> Prop) s t).
Proof. exact (@lem3477506 (@I ((_90228 -> Prop) -> Prop) s t)). Qed.
Lemma lem3477508 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : @I ((_90228 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3477507 _90228 s t) (@lem3477504 _90228 s u t x h1)). Qed.
Lemma lem3477510 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) (h1 : @I (_90228 -> Prop) t x) : @I (_90228 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3477511 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) (h1 : @I (_90228 -> Prop) t x) : term300 _90228 t x.
Proof. exact (fun h0 : term269 _90228 t x => @lem3477510 _90228 t x h1). Qed.
Lemma lem3477513 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477514 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (term300 _90228 t x) = (@I (_90228 -> Prop) t x).
Proof. exact (@lem3477513 (@I (_90228 -> Prop) t x)). Qed.
Lemma lem3477515 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) (h1 : @I (_90228 -> Prop) t x) : @I (_90228 -> Prop) t x.
Proof. exact (EQ_MP (@lem3477514 _90228 t x) (@lem3477511 _90228 t x h1)). Qed.
Lemma lem3477517 (a : Prop) (b : Prop) : (term305 a b) = (term306 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3477518 {_90228 : Type'} (s : type686 _90228) (_36683 : _90228 -> Prop) (x : _90228) : (term286 _90228 s _36683 x) = (term307 _90228 s _36683 x).
Proof. exact (@lem3477517 (@I ((_90228 -> Prop) -> Prop) s _36683) (@I (_90228 -> Prop) _36683 x)). Qed.
Lemma lem3477520 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3477521 {_90228 : Type'} (s : type686 _90228) (_36683 : _90228 -> Prop) (x : _90228) : (term307 _90228 s _36683 x) = (term308 _90228 s _36683 x).
Proof. exact (@lem3477520 (term279 _90228 s _36683 x)). Qed.
Lemma lem3477522 {_90228 : Type'} (s : type686 _90228) (_36683 : _90228 -> Prop) (x : _90228) : (term286 _90228 s _36683 x) = (term308 _90228 s _36683 x).
Proof. exact (TRANS (@lem3477518 _90228 s _36683 x) (@lem3477521 _90228 s _36683 x)). Qed.
Lemma lem3477524 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : term279 _90228 s t x.
Proof. exact (conj (@lem3477508 _90228 s u t x h1) (@lem3477515 _90228 t x h2)). Qed.
Lemma lem3477526 {_90228 : Type'} (_36683 : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term308 _90228 s _36683 x.
Proof. exact (EQ_MP (@lem3477522 _90228 s _36683 x) (@lem3477442 _90228 _36683 s u t x h1)). Qed.
Lemma lem3477527 {_90228 : Type'} (_36683 : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term308 _90228 s _36683 x.
Proof. exact (@lem3477526 _90228 _36683 s u t x h1). Qed.
Lemma lem3477528 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : term308 _90228 s t x.
Proof. exact (@lem3477527 _90228 t s u t x h1). Qed.
Lemma lem3477531 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : False.
Proof. exact (@lem3477528 _90228 s u t x h1 (@lem3477524 _90228 s u t x h1 h2)). Qed.
Lemma lem3477532 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : term303.
Proof. exact (fun h0 : ~ False => @lem3477531 _90228 s u t x h1 h2). Qed.
Lemma lem3477534 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477535 : term303 = False.
Proof. exact (@lem3477534 False). Qed.
Lemma lem3477536 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3477535) (@lem3477532 _90228 s u t x h1 h2)). Qed.
Lemma lem3477538 {_90228 : Type'} (s : type686 _90228) (x' : _90228 -> Prop) (h1 : s x') : @I ((_90228 -> Prop) -> Prop) s x'.
Proof. exact (EQ_MP (@lem3477259 _90228 s x') (@lem3477103 _90228 s x' h1)). Qed.
Lemma lem3477539 {_90228 : Type'} (s : type686 _90228) (x' : _90228 -> Prop) (h1 : s x') : term304 _90228 s x'.
Proof. exact (fun h0 : term272 _90228 s x' => @lem3477538 _90228 s x' h1). Qed.
Lemma lem3477541 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477542 {_90228 : Type'} (s : type686 _90228) (x' : _90228 -> Prop) : (term304 _90228 s x') = (@I ((_90228 -> Prop) -> Prop) s x').
Proof. exact (@lem3477541 (@I ((_90228 -> Prop) -> Prop) s x')). Qed.
Lemma lem3477543 {_90228 : Type'} (s : type686 _90228) (x' : _90228 -> Prop) (h1 : s x') : @I ((_90228 -> Prop) -> Prop) s x'.
Proof. exact (EQ_MP (@lem3477542 _90228 s x') (@lem3477539 _90228 s x' h1)). Qed.
Lemma lem3477549 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3477550 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : (term299 _90228 s _36684 u x) = (term309 _90228 u x s _36684).
Proof. exact (@lem3477549 (@I (_90228 -> Prop) u x) (term272 _90228 s _36684)). Qed.
Lemma lem3477556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3477557 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : (term310 _90228 s _36684 u x) = (term311 _90228 u x s _36684).
Proof. exact (MK_COMB (@lem3477556) (@lem3477550 _90228 u x s _36684)). Qed.
Lemma lem3477563 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : (term309 _90228 u x s _36684) = (term309 _90228 u x s _36684).
Proof. exact (eq_refl (term309 _90228 u x s _36684)). Qed.
Lemma lem3477564 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : ((term299 _90228 s _36684 u x) = (term309 _90228 u x s _36684)) = ((term309 _90228 u x s _36684) = (term309 _90228 u x s _36684)).
Proof. exact (MK_COMB (@lem3477557 _90228 u x s _36684) (@lem3477563 _90228 u x s _36684)). Qed.
Lemma lem3477566 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3477567 (x : Prop) : (x = x) = True.
Proof. exact (@lem3477566 Prop x). Qed.
Lemma lem3477568 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : ((term309 _90228 u x s _36684) = (term309 _90228 u x s _36684)) = True.
Proof. exact (@lem3477567 (term309 _90228 u x s _36684)). Qed.
Lemma lem3477569 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : ((term299 _90228 s _36684 u x) = (term309 _90228 u x s _36684)) = True.
Proof. exact (TRANS (@lem3477564 _90228 u x s _36684) (@lem3477568 _90228 u x s _36684)). Qed.
Lemma lem3477570 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : True = ((term299 _90228 s _36684 u x) = (term309 _90228 u x s _36684)).
Proof. exact (SYM (@lem3477569 _90228 u x s _36684)). Qed.
Lemma lem3477571 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (_36684 : _90228 -> Prop) : (term299 _90228 s _36684 u x) = (term309 _90228 u x s _36684).
Proof. exact (EQ_MP (@lem3477570 _90228 u x s _36684) (@lem0)). Qed.
Lemma lem3477572 {_90228 : Type'} (_36684 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term309 _90228 u x s _36684.
Proof. exact (EQ_MP (@lem3477571 _90228 u x s _36684) (@lem3477454 _90228 _36684 t s u x h1)). Qed.
Lemma lem3477574 (b : Prop) (a : Prop) : (a \/ b) = (term312 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3477575 {_90228 : Type'} (s : type686 _90228) (_36684 : _90228 -> Prop) (u : _90228 -> Prop) (x : _90228) : (term309 _90228 u x s _36684) = (term313 _90228 s _36684 u x).
Proof. exact (@lem3477574 (term272 _90228 s _36684) (@I (_90228 -> Prop) u x)). Qed.
Lemma lem3477577 (a : Prop) : (term137 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3477578 {_90228 : Type'} (s : type686 _90228) (_36684 : _90228 -> Prop) : (term314 _90228 s _36684) = (@I ((_90228 -> Prop) -> Prop) s _36684).
Proof. exact (@lem3477577 (@I ((_90228 -> Prop) -> Prop) s _36684)). Qed.
Lemma lem3477579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3477580 {_90228 : Type'} (s : type686 _90228) (_36684 : _90228 -> Prop) : (term315 _90228 s _36684) = (term316 _90228 s _36684).
Proof. exact (MK_COMB (@lem3477579) (@lem3477578 _90228 s _36684)). Qed.
Lemma lem3477581 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (@I (_90228 -> Prop) u x) = (@I (_90228 -> Prop) u x).
Proof. exact (eq_refl (@I (_90228 -> Prop) u x)). Qed.
Lemma lem3477582 {_90228 : Type'} (s : type686 _90228) (_36684 : _90228 -> Prop) (u : _90228 -> Prop) (x : _90228) : (term313 _90228 s _36684 u x) = (term317 _90228 s _36684 u x).
Proof. exact (MK_COMB (@lem3477580 _90228 s _36684) (@lem3477581 _90228 u x)). Qed.
Lemma lem3477583 {_90228 : Type'} (s : type686 _90228) (_36684 : _90228 -> Prop) (u : _90228 -> Prop) (x : _90228) : (term309 _90228 u x s _36684) = (term317 _90228 s _36684 u x).
Proof. exact (TRANS (@lem3477575 _90228 s _36684 u x) (@lem3477582 _90228 s _36684 u x)). Qed.
Lemma lem3477586 {_90228 : Type'} (_36684 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term317 _90228 s _36684 u x.
Proof. exact (EQ_MP (@lem3477583 _90228 s _36684 u x) (@lem3477572 _90228 _36684 t s u x h1)). Qed.
Lemma lem3477587 {_90228 : Type'} (_36684 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term317 _90228 s _36684 u x.
Proof. exact (@lem3477586 _90228 _36684 t s u x h1). Qed.
Lemma lem3477588 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term317 _90228 s x' u x.
Proof. exact (@lem3477587 _90228 x' t s u x h1). Qed.
Lemma lem3477591 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : s x') (h2 : term283 _90228 t s u x) : @I (_90228 -> Prop) u x.
Proof. exact (@lem3477588 _90228 x' t s u x h2 (@lem3477543 _90228 s x' h1)). Qed.
Lemma lem3477592 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : s x') (h2 : term283 _90228 t s u x) : term300 _90228 u x.
Proof. exact (fun h0 : term269 _90228 u x => @lem3477591 _90228 x' t s u x h1 h2). Qed.
Lemma lem3477594 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477595 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term300 _90228 u x) = (@I (_90228 -> Prop) u x).
Proof. exact (@lem3477594 (@I (_90228 -> Prop) u x)). Qed.
Lemma lem3477596 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : s x') (h2 : term283 _90228 t s u x) : @I (_90228 -> Prop) u x.
Proof. exact (EQ_MP (@lem3477595 _90228 u x) (@lem3477592 _90228 x' t s u x h1 h2)). Qed.
Lemma lem3477599 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3477601 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) : (term269 _90228 u x) = (term302 _90228 u x).
Proof. exact (@lem3477599 (@I (_90228 -> Prop) u x)). Qed.
Lemma lem3477604 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) : term302 _90228 u x.
Proof. exact (EQ_MP (@lem3477601 _90228 u x) (@lem3477448 _90228 u x h1)). Qed.
Lemma lem3477607 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : False.
Proof. exact (@lem3477604 _90228 u x h1 (@lem3477596 _90228 x' t s u x h2 h3)). Qed.
Lemma lem3477608 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : term303.
Proof. exact (fun h0 : ~ False => @lem3477607 _90228 x' t s u x h1 h2 h3). Qed.
Lemma lem3477610 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477611 : term303 = False.
Proof. exact (@lem3477610 False). Qed.
Lemma lem3477612 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : False.
Proof. exact (EQ_MP (@lem3477611) (@lem3477608 _90228 x' t s u x h1 h2 h3)). Qed.
Lemma lem3477614 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : @I ((_90228 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3477274 _90228 s t x h1)). Qed.
Lemma lem3477615 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : term304 _90228 s t.
Proof. exact (fun h0 : term272 _90228 s t => @lem3477614 _90228 s t x h1). Qed.
Lemma lem3477617 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477618 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) : (term304 _90228 s t) = (@I ((_90228 -> Prop) -> Prop) s t).
Proof. exact (@lem3477617 (@I ((_90228 -> Prop) -> Prop) s t)). Qed.
Lemma lem3477619 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : @I ((_90228 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3477618 _90228 s t) (@lem3477615 _90228 s t x h1)). Qed.
Lemma lem3477621 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : @I (_90228 -> Prop) t x.
Proof. exact (proj2 (@lem3477274 _90228 s t x h1)). Qed.
Lemma lem3477622 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : term300 _90228 t x.
Proof. exact (fun h0 : term269 _90228 t x => @lem3477621 _90228 s t x h1). Qed.
Lemma lem3477624 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477625 {_90228 : Type'} (t : _90228 -> Prop) (x : _90228) : (term300 _90228 t x) = (@I (_90228 -> Prop) t x).
Proof. exact (@lem3477624 (@I (_90228 -> Prop) t x)). Qed.
Lemma lem3477626 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : @I (_90228 -> Prop) t x.
Proof. exact (EQ_MP (@lem3477625 _90228 t x) (@lem3477622 _90228 s t x h1)). Qed.
Lemma lem3477628 (a : Prop) (b : Prop) : (term305 a b) = (term306 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3477629 {_90228 : Type'} (s : type686 _90228) (_36685 : _90228 -> Prop) (x : _90228) : (term286 _90228 s _36685 x) = (term307 _90228 s _36685 x).
Proof. exact (@lem3477628 (@I ((_90228 -> Prop) -> Prop) s _36685) (@I (_90228 -> Prop) _36685 x)). Qed.
Lemma lem3477631 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3477632 {_90228 : Type'} (s : type686 _90228) (_36685 : _90228 -> Prop) (x : _90228) : (term307 _90228 s _36685 x) = (term308 _90228 s _36685 x).
Proof. exact (@lem3477631 (term279 _90228 s _36685 x)). Qed.
Lemma lem3477633 {_90228 : Type'} (s : type686 _90228) (_36685 : _90228 -> Prop) (x : _90228) : (term286 _90228 s _36685 x) = (term308 _90228 s _36685 x).
Proof. exact (TRANS (@lem3477629 _90228 s _36685 x) (@lem3477632 _90228 s _36685 x)). Qed.
Lemma lem3477635 {_90228 : Type'} (s : type686 _90228) (t : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) : term279 _90228 s t x.
Proof. exact (conj (@lem3477619 _90228 s t x h1) (@lem3477626 _90228 s t x h1)). Qed.
Lemma lem3477637 {_90228 : Type'} (_36685 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term308 _90228 s _36685 x.
Proof. exact (EQ_MP (@lem3477633 _90228 s _36685 x) (@lem3477478 _90228 _36685 t s u x h1)). Qed.
Lemma lem3477638 {_90228 : Type'} (_36685 : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term308 _90228 s _36685 x.
Proof. exact (@lem3477637 _90228 _36685 t s u x h1). Qed.
Lemma lem3477639 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term283 _90228 t s u x) : term308 _90228 s t x.
Proof. exact (@lem3477638 _90228 t t s u x h1). Qed.
Lemma lem3477642 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) (h2 : term283 _90228 t s u x) : False.
Proof. exact (@lem3477639 _90228 t s u x h2 (@lem3477635 _90228 s t x h1)). Qed.
Lemma lem3477643 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) (h2 : term283 _90228 t s u x) : term303.
Proof. exact (fun h0 : ~ False => @lem3477642 _90228 t s u x h1 h2). Qed.
Lemma lem3477645 (p : Prop) : (term301 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3477646 : term303 = False.
Proof. exact (@lem3477645 False). Qed.
Lemma lem3477647 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term279 _90228 s t x) (h2 : term283 _90228 t s u x) : False.
Proof. exact (EQ_MP (@lem3477646) (@lem3477643 _90228 t s u x h1 h2)). Qed.
Lemma lem3477648 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : (term269 _90228 u x) = False.
Proof. exact (prop_ext (fun h4 : term269 _90228 u x => @lem3477612 _90228 x' t s u x h1 h2 h3) (fun h4 : False => @lem3477448 _90228 u x h1)). Qed.
Lemma lem3477649 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : False.
Proof. exact (EQ_MP (@lem3477648 _90228 x' t s u x h1 h2 h3) (@lem3477448 _90228 u x h1)). Qed.
Lemma lem3477650 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : (@I (_90228 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_90228 -> Prop) t x => @lem3477536 _90228 s u t x h1 h2) (fun h3 : False => @lem3477444 _90228 t x h2)). Qed.
Lemma lem3477651 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3477650 _90228 s u t x h1 h2) (@lem3477444 _90228 t x h2)). Qed.
Lemma lem3477652 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : (term269 _90228 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90228 u x => @lem3477501 _90228 s u t x h1 h2) (fun h3 : False => @lem3477430 _90228 u x h1)). Qed.
Lemma lem3477653 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : False.
Proof. exact (EQ_MP (@lem3477652 _90228 s u t x h1 h2) (@lem3477430 _90228 u x h1)). Qed.
Lemma lem3477654 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : (term269 _90228 u x) = False.
Proof. exact (prop_ext (fun h4 : term269 _90228 u x => @lem3477649 _90228 x' t s u x h1 h2 h3) (fun h4 : False => @lem3477365 _90228 u x h1)). Qed.
Lemma lem3477655 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : False.
Proof. exact (EQ_MP (@lem3477654 _90228 x' t s u x h1 h2 h3) (@lem3477365 _90228 u x h1)). Qed.
Lemma lem3477656 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : (@I (_90228 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_90228 -> Prop) t x => @lem3477651 _90228 s u t x h1 h2) (fun h3 : False => @lem3477334 _90228 t x h2)). Qed.
Lemma lem3477657 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3477656 _90228 s u t x h1 h2) (@lem3477334 _90228 t x h2)). Qed.
Lemma lem3477658 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : (term269 _90228 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90228 u x => @lem3477653 _90228 s u t x h1 h2) (fun h3 : False => @lem3477305 _90228 u x h1)). Qed.
Lemma lem3477659 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : False.
Proof. exact (EQ_MP (@lem3477658 _90228 s u t x h1 h2) (@lem3477305 _90228 u x h1)). Qed.
Lemma lem3477660 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : (term269 _90228 u x) = False.
Proof. exact (prop_ext (fun h4 : term269 _90228 u x => @lem3477655 _90228 x' t s u x h1 h2 h3) (fun h4 : False => @lem3477365 _90228 u x h1)). Qed.
Lemma lem3477661 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : s x') (h3 : term283 _90228 t s u x) : False.
Proof. exact (EQ_MP (@lem3477660 _90228 x' t s u x h1 h2 h3) (@lem3477365 _90228 u x h1)). Qed.
Lemma lem3477662 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : (@I (_90228 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_90228 -> Prop) t x => @lem3477657 _90228 s u t x h1 h2) (fun h3 : False => @lem3477334 _90228 t x h2)). Qed.
Lemma lem3477663 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) (h2 : @I (_90228 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3477662 _90228 s u t x h1 h2) (@lem3477334 _90228 t x h2)). Qed.
Lemma lem3477664 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : (term269 _90228 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90228 u x => @lem3477659 _90228 s u t x h1 h2) (fun h3 : False => @lem3477305 _90228 u x h1)). Qed.
Lemma lem3477665 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term269 _90228 u x) (h2 : term291 _90228 s u t x) : False.
Proof. exact (EQ_MP (@lem3477664 _90228 s u t x h1 h2) (@lem3477305 _90228 u x h1)). Qed.
Lemma lem3477666 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : s x') (h2 : term283 _90228 t s u x) : False.
Proof. exact (or_elim (@lem3477272 _90228 t s u x h2) (fun h0 : term269 _90228 u x => @lem3477661 _90228 x' t s u x h0 h1 h2) (fun h0 : term279 _90228 s t x => @lem3477647 _90228 t s u x h0 h2)). Qed.
Lemma lem3477667 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (t : _90228 -> Prop) (x : _90228) (h1 : term291 _90228 s u t x) : False.
Proof. exact (or_elim (@lem3477265 _90228 s u t x h1) (fun h0 : term269 _90228 u x => @lem3477665 _90228 s u t x h0 h1) (fun h0 : @I (_90228 -> Prop) t x => @lem3477663 _90228 s u t x h1 h0)). Qed.
Lemma lem3477668 {_90228 : Type'} (x' : _90228 -> Prop) (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : s x') (h2 : term265 _90228 t s u x) : False.
Proof. exact (or_elim (@lem3477251 _90228 t s u x h2) (fun h0 : term291 _90228 s u t x => @lem3477667 _90228 s u t x h0) (fun h0 : term283 _90228 t s u x => @lem3477666 _90228 x' t s u x h1 h0)). Qed.
Lemma lem3477669 {_90228 : Type'} (t : _90228 -> Prop) (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term81 _90228 s) (h2 : term265 _90228 t s u x) : False.
Proof. exact (ex_elim (@lem3476758 _90228 s h1) (fun x' : _90228 -> Prop => fun h0 : term147 _90228 s x' => @lem3477668 _90228 x' t s u x h0 h2)). Qed.
Lemma lem3477670 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term81 _90228 s) (h2 : term139 _90228 s u x) : False.
Proof. exact (ex_elim (@lem3477101 _90228 s u x h2) (fun t : _90228 -> Prop => fun h0 : term267 _90228 s u x t => @lem3477669 _90228 t s u x h1 h0)). Qed.
Lemma lem3477671 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term81 _90228 s) (h2 : term139 _90228 s u x) : (term139 _90228 s u x) = False.
Proof. exact (prop_ext (fun h3 : term139 _90228 s u x => @lem3477670 _90228 s u x h1 h2) (fun h3 : False => @lem3476736 _90228 s u x h2)). Qed.
Lemma lem3477672 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) (x : _90228) (h1 : term81 _90228 s) (h2 : term139 _90228 s u x) : False.
Proof. exact (EQ_MP (@lem3477671 _90228 s u x h1 h2) (@lem3476736 _90228 s u x h2)). Qed.
Lemma lem3477673 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (h1 : term81 _90228 s) : term138 _90228 s u x.
Proof. exact (fun h0 : term139 _90228 s u x => @lem3477672 _90228 s u x h1 h0). Qed.
Lemma lem3477674 {_90228 : Type'} (u : _90228 -> Prop) (x : _90228) (s : type686 _90228) (h1 : term81 _90228 s) : (term99 _90228 u s x) = (term121 _90228 s u x).
Proof. exact (EQ_MP (@lem3476735 _90228 s u x) (@lem3477673 _90228 u x s h1)). Qed.
Lemma lem3477679 {_90228 : Type'} (u : _90228 -> Prop) (s : type686 _90228) (h1 : term81 _90228 s) : term124 _90228 s u.
Proof. exact (fun x : _90228 => @lem3477674 _90228 u x s h1). Qed.
Lemma lem3477680 {_90228 : Type'} (s : type686 _90228) (u : _90228 -> Prop) : term125 _90228 s u.
Proof. exact (fun h0 : term81 _90228 s => @lem3477679 _90228 u s h0). Qed.
Lemma lem3477685 {_90228 : Type'} (u : _90228 -> Prop) : term127 _90228 u.
Proof. exact (fun s : type686 _90228 => @lem3477680 _90228 s u). Qed.
Lemma lem3477690 {_90228 : Type'} : term129 _90228.
Proof. exact (fun u : _90228 -> Prop => @lem3477685 _90228 u). Qed.
Lemma lem3477691 {_90228 : Type'} : term131 _90228.
Proof. exact (EQ_MP (@lem3476730 _90228) (@lem3477690 _90228)). Qed.
Lemma lem3477693 {_90228 : Type'} : term131 _90228.
Proof. exact (@lem3476560 _90228 (@lem3477691 _90228)). Qed.
Lemma lem3477694 {_90228 : Type'} (h1 : term132 _90228) : False.
Proof. exact (@lem3477693 _90228 (@lem3476544 _90228 h1)). Qed.
Lemma lem3477695 {_90228 : Type'} (h1 : term132 _90228) : (term132 _90228) = False.
Proof. exact (prop_ext (fun h2 : term132 _90228 => @lem3477694 _90228 h1) (fun h2 : False => @lem3476544 _90228 h1)). Qed.
Lemma lem3477696 {_90228 : Type'} (h1 : term132 _90228) : False.
Proof. exact (EQ_MP (@lem3477695 _90228 h1) (@lem3476544 _90228 h1)). Qed.
Lemma lem3477697 {_90228 : Type'} : term131 _90228.
Proof. exact (fun h0 : term132 _90228 => @lem3477696 _90228 h0). Qed.
Lemma lem3477698 {_90228 : Type'} : term129 _90228.
Proof. exact (EQ_MP (@lem3476543 _90228) (@lem3477697 _90228)). Qed.
Lemma lem3477699 {_90228 : Type'} : term74 _90228.
Proof. exact (EQ_MP (@lem3476539 _90228) (@lem3477698 _90228)). Qed.
Lemma lem3477700 {_90228 : Type'} : term62 _90228.
Proof. exact (EQ_MP (@lem3476347 _90228) (@lem3477699 _90228)). Qed.
Lemma lem3477701 {_90228 : Type'} : term61 _90228.
Proof. exact (EQ_MP (@lem3476277 _90228) (@lem3477700 _90228)). Qed.
