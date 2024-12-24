Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EQ_CLAUSES_term_abbrevs.
Require Import NOT_DEF_spec.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm43_spec.
Require Import thm69_spec.
Require Import thm98_spec.
Lemma lem1266 (t : Prop) (h1 : True = t) : True = t.
Proof. exact (h1). Qed.
Lemma lem1267 (t : Prop) : term0 t.
Proof. exact (@lem43 t True). Qed.
Lemma lem1269 (t : Prop) : term1 t.
Proof. exact (@lem37 True t). Qed.
Lemma lem1272 (t : Prop) (h1 : True = t) : t -> True.
Proof. exact (@lem1267 t (@lem1266 t h1)). Qed.
Lemma lem1273 (t : Prop) (h1 : True = t) : True -> t.
Proof. exact (@lem1269 t (@lem1266 t h1)). Qed.
Lemma lem1275 (t : Prop) (h1 : True -> t) : True -> t.
Proof. exact (h1). Qed.
Lemma lem1276 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem1277 (t : Prop) (h1 : True) (h2 : True -> t) : t.
Proof. exact (@lem1275 t h2 (@lem1276 h1)). Qed.
Lemma lem1278 (t : Prop) (h1 : True -> t) : True = t.
Proof. exact (prop_ext (fun h2 : True => @lem1277 t h2 h1) (fun h2 : t => @lem0)). Qed.
Lemma lem1279 (t : Prop) (h1 : True -> t) : t.
Proof. exact (EQ_MP (@lem1278 t h1) (@lem0)). Qed.
Lemma lem1280 (t : Prop) : term2 t.
Proof. exact (fun h0 : True -> t => @lem1279 t h0). Qed.
Lemma lem1281 (t : Prop) : term3 t.
Proof. exact (fun h0 : t -> True => @lem1280 t). Qed.
Lemma lem1282 (t : Prop) (h1 : True = t) : term2 t.
Proof. exact (@lem1281 t (@lem1272 t h1)). Qed.
Lemma lem1283 (t : Prop) (h1 : True = t) : t.
Proof. exact (@lem1282 t h1 (@lem1273 t h1)). Qed.
Lemma lem1284 (t : Prop) : term4 t.
Proof. exact (fun h0 : True = t => @lem1283 t h0). Qed.
Lemma lem1285 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1287 (t : Prop) (h1 : t) : True -> t.
Proof. exact (fun h0 : True => @lem1285 t h1). Qed.
Lemma lem1289 (t : Prop) : t -> True.
Proof. exact (fun h0 : t => @lem0). Qed.
Lemma lem1290 (t : Prop) (h1 : t) : term5 t.
Proof. exact (conj (@lem1287 t h1) (@lem1289 t)). Qed.
Lemma lem1291 (t : Prop) : (term5 t) = (True = t).
Proof. exact (@lem32 True t). Qed.
Lemma lem1292 (t : Prop) (h1 : t) : True = t.
Proof. exact (EQ_MP (@lem1291 t) (@lem1290 t h1)). Qed.
Lemma lem1293 (t : Prop) : term6 t.
Proof. exact (fun h0 : t => @lem1292 t h0). Qed.
Lemma lem1294 (t : Prop) : term7 t.
Proof. exact (conj (@lem1284 t) (@lem1293 t)). Qed.
Lemma lem1295 (t : Prop) : (term7 t) = ((True = t) = t).
Proof. exact (@lem32 (True = t) t). Qed.
Lemma lem1296 (t : Prop) : (True = t) = t.
Proof. exact (EQ_MP (@lem1295 t) (@lem1294 t)). Qed.
Lemma lem1297 (t : Prop) (h1 : t = True) : t = True.
Proof. exact (h1). Qed.
Lemma lem1298 (t : Prop) : term8 t.
Proof. exact (@lem43 True t). Qed.
Lemma lem1300 (t : Prop) : term9 t.
Proof. exact (@lem37 t True). Qed.
Lemma lem1303 (t : Prop) (h1 : t = True) : True -> t.
Proof. exact (@lem1298 t (@lem1297 t h1)). Qed.
Lemma lem1304 (t : Prop) (h1 : t = True) : t -> True.
Proof. exact (@lem1300 t (@lem1297 t h1)). Qed.
Lemma lem1305 (t : Prop) (h1 : True -> t) : True -> t.
Proof. exact (h1). Qed.
Lemma lem1313 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem1314 (t : Prop) (h1 : True) (h2 : True -> t) : t.
Proof. exact (@lem1305 t h2 (@lem1313 h1)). Qed.
Lemma lem1315 (t : Prop) (h1 : True -> t) : True = t.
Proof. exact (prop_ext (fun h2 : True => @lem1314 t h2 h1) (fun h2 : t => @lem0)). Qed.
Lemma lem1316 (t : Prop) (h1 : True -> t) : t.
Proof. exact (EQ_MP (@lem1315 t h1) (@lem0)). Qed.
Lemma lem1317 (t : Prop) (h1 : True -> t) : term10 t.
Proof. exact (fun h0 : t -> True => @lem1316 t h1). Qed.
Lemma lem1318 (t : Prop) : term11 t.
Proof. exact (fun h0 : True -> t => @lem1317 t h0). Qed.
Lemma lem1319 (t : Prop) (h1 : t = True) : term10 t.
Proof. exact (@lem1318 t (@lem1303 t h1)). Qed.
Lemma lem1320 (t : Prop) (h1 : t = True) : t.
Proof. exact (@lem1319 t h1 (@lem1304 t h1)). Qed.
Lemma lem1321 (t : Prop) : term12 t.
Proof. exact (fun h0 : t = True => @lem1320 t h0). Qed.
Lemma lem1322 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1324 (t : Prop) : t -> True.
Proof. exact (fun h0 : t => @lem0). Qed.
Lemma lem1326 (t : Prop) (h1 : t) : True -> t.
Proof. exact (fun h0 : True => @lem1322 t h1). Qed.
Lemma lem1327 (t : Prop) (h1 : t) : term13 t.
Proof. exact (conj (@lem1324 t) (@lem1326 t h1)). Qed.
Lemma lem1328 (t : Prop) : (term13 t) = (t = True).
Proof. exact (@lem32 t True). Qed.
Lemma lem1329 (t : Prop) (h1 : t) : t = True.
Proof. exact (EQ_MP (@lem1328 t) (@lem1327 t h1)). Qed.
Lemma lem1330 (t : Prop) : term14 t.
Proof. exact (fun h0 : t => @lem1329 t h0). Qed.
Lemma lem1331 (t : Prop) : term15 t.
Proof. exact (conj (@lem1321 t) (@lem1330 t)). Qed.
Lemma lem1332 (t : Prop) : (term15 t) = ((t = True) = t).
Proof. exact (@lem32 (t = True) t). Qed.
Lemma lem1333 (t : Prop) : (t = True) = t.
Proof. exact (EQ_MP (@lem1332 t) (@lem1331 t)). Qed.
Lemma lem1334 (t : Prop) (h1 : False = t) : False = t.
Proof. exact (h1). Qed.
Lemma lem1335 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1336 (t : Prop) : term16 t.
Proof. exact (@lem43 t False). Qed.
Lemma lem1338 (t : Prop) : term17 t.
Proof. exact (@lem37 False t). Qed.
Lemma lem1341 (t : Prop) (h1 : False = t) : t -> False.
Proof. exact (@lem1336 t (@lem1334 t h1)). Qed.
Lemma lem1342 (t : Prop) (h1 : False = t) : False -> t.
Proof. exact (@lem1338 t (@lem1334 t h1)). Qed.
Lemma lem1343 (t : Prop) (h1 : t -> False) : t -> False.
Proof. exact (h1). Qed.
Lemma lem1351 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1352 (t : Prop) (h1 : t) (h2 : t -> False) : False.
Proof. exact (@lem1343 t h2 (@lem1351 t h1)). Qed.
Lemma lem1353 (t : Prop) (h1 : t) (h2 : t -> False) : t = False.
Proof. exact (prop_ext (fun h3 : t => @lem1352 t h1 h2) (fun h3 : False => @lem1335 t h1)). Qed.
Lemma lem1354 (t : Prop) (h1 : t) (h2 : t -> False) : False.
Proof. exact (EQ_MP (@lem1353 t h1 h2) (@lem1335 t h1)). Qed.
Lemma lem1355 (t : Prop) (h1 : t) (h2 : t -> False) : term18 t.
Proof. exact (fun h0 : False -> t => @lem1354 t h1 h2). Qed.
Lemma lem1356 (t : Prop) (h1 : t) : term19 t.
Proof. exact (fun h0 : t -> False => @lem1355 t h1 h0). Qed.
Lemma lem1357 (t : Prop) (h1 : t) (h2 : False = t) : term18 t.
Proof. exact (@lem1356 t h1 (@lem1341 t h2)). Qed.
Lemma lem1358 (t : Prop) (h1 : t) (h2 : False = t) : False.
Proof. exact (@lem1357 t h1 h2 (@lem1342 t h2)). Qed.
Lemma lem1359 (t : Prop) (h1 : False = t) : t -> False.
Proof. exact (fun h0 : t => @lem1358 t h0 h1). Qed.
Lemma lem1360 (t : Prop) : (t -> False) = (~ t).
Proof. exact (@lem69 t). Qed.
Lemma lem1361 (t : Prop) (h1 : False = t) : ~ t.
Proof. exact (EQ_MP (@lem1360 t) (@lem1359 t h1)). Qed.
Lemma lem1362 (t : Prop) : term20 t.
Proof. exact (fun h0 : False = t => @lem1361 t h0). Qed.
Lemma lem1363 (t : Prop) (h1 : ~ t) : ~ t.
Proof. exact (h1). Qed.
Lemma lem1364 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1365 (t : Prop) (h1 : False) : t.
Proof. exact (@lem98 t h1). Qed.
Lemma lem1366 (t : Prop) (h1 : False) : False = t.
Proof. exact (prop_ext (fun h2 : False => @lem1365 t h1) (fun h2 : t => @lem1364 h1)). Qed.
Lemma lem1367 (t : Prop) (h1 : False) : t.
Proof. exact (EQ_MP (@lem1366 t h1) (@lem1364 h1)). Qed.
Lemma lem1368 (t : Prop) : False -> t.
Proof. exact (fun h0 : False => @lem1367 t h0). Qed.
Lemma lem1369 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1370 (t : Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1371 (t : Prop) : (~ t) = (term21 t).
Proof. exact (MK_COMB (@lem56) (@lem1370 t)). Qed.
Lemma lem1372 (t : Prop) : (term21 t) = (t -> False).
Proof. exact (eq_refl (term21 t)). Qed.
Lemma lem1373 (t : Prop) : (term22 t) = (term22 t).
Proof. exact (eq_refl (term22 t)). Qed.
Lemma lem1374 (t : Prop) : ((~ t) = (term21 t)) = ((~ t) = (t -> False)).
Proof. exact (MK_COMB (@lem1373 t) (@lem1372 t)). Qed.
Lemma lem1375 (t : Prop) : (~ t) = (t -> False).
Proof. exact (EQ_MP (@lem1374 t) (@lem1371 t)). Qed.
Lemma lem1376 (t : Prop) (h1 : ~ t) : t -> False.
Proof. exact (EQ_MP (@lem1375 t) (@lem1363 t h1)). Qed.
Lemma lem1377 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1378 (t : Prop) (h1 : t) (h2 : ~ t) : False.
Proof. exact (@lem1376 t h2 (@lem1377 t h1)). Qed.
Lemma lem1379 (t : Prop) (h1 : t) (h2 : ~ t) : t = False.
Proof. exact (prop_ext (fun h3 : t => @lem1378 t h1 h2) (fun h3 : False => @lem1369 t h1)). Qed.
Lemma lem1380 (t : Prop) (h1 : t) (h2 : ~ t) : False.
Proof. exact (EQ_MP (@lem1379 t h1 h2) (@lem1369 t h1)). Qed.
Lemma lem1381 (t : Prop) (h1 : ~ t) : t -> False.
Proof. exact (fun h0 : t => @lem1380 t h0 h1). Qed.
Lemma lem1382 (t : Prop) (h1 : ~ t) : term23 t.
Proof. exact (conj (@lem1368 t) (@lem1381 t h1)). Qed.
Lemma lem1383 (t : Prop) : (term23 t) = (False = t).
Proof. exact (@lem32 False t). Qed.
Lemma lem1384 (t : Prop) (h1 : ~ t) : False = t.
Proof. exact (EQ_MP (@lem1383 t) (@lem1382 t h1)). Qed.
Lemma lem1385 (t : Prop) : term24 t.
Proof. exact (fun h0 : ~ t => @lem1384 t h0). Qed.
Lemma lem1386 (t : Prop) : term25 t.
Proof. exact (conj (@lem1362 t) (@lem1385 t)). Qed.
Lemma lem1387 (t : Prop) : (term25 t) = ((False = t) = (~ t)).
Proof. exact (@lem32 (False = t) (~ t)). Qed.
Lemma lem1388 (t : Prop) : (False = t) = (~ t).
Proof. exact (EQ_MP (@lem1387 t) (@lem1386 t)). Qed.
Lemma lem1389 (t : Prop) (h1 : t = False) : t = False.
Proof. exact (h1). Qed.
Lemma lem1390 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1391 (t : Prop) : term26 t.
Proof. exact (@lem43 False t). Qed.
Lemma lem1393 (t : Prop) : term27 t.
Proof. exact (@lem37 t False). Qed.
Lemma lem1396 (t : Prop) (h1 : t = False) : False -> t.
Proof. exact (@lem1391 t (@lem1389 t h1)). Qed.
Lemma lem1397 (t : Prop) (h1 : t = False) : t -> False.
Proof. exact (@lem1393 t (@lem1389 t h1)). Qed.
Lemma lem1399 (t : Prop) (h1 : t -> False) : t -> False.
Proof. exact (h1). Qed.
Lemma lem1400 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1401 (t : Prop) (h1 : t) (h2 : t -> False) : False.
Proof. exact (@lem1399 t h2 (@lem1400 t h1)). Qed.
Lemma lem1402 (t : Prop) (h1 : t) (h2 : t -> False) : t = False.
Proof. exact (prop_ext (fun h3 : t => @lem1401 t h1 h2) (fun h3 : False => @lem1390 t h1)). Qed.
Lemma lem1403 (t : Prop) (h1 : t) (h2 : t -> False) : False.
Proof. exact (EQ_MP (@lem1402 t h1 h2) (@lem1390 t h1)). Qed.
Lemma lem1404 (t : Prop) (h1 : t) : term28 t.
Proof. exact (fun h0 : t -> False => @lem1403 t h1 h0). Qed.
Lemma lem1405 (t : Prop) (h1 : t) : term29 t.
Proof. exact (fun h0 : False -> t => @lem1404 t h1). Qed.
Lemma lem1406 (t : Prop) (h1 : t) (h2 : t = False) : term28 t.
Proof. exact (@lem1405 t h1 (@lem1396 t h2)). Qed.
Lemma lem1407 (t : Prop) (h1 : t) (h2 : t = False) : False.
Proof. exact (@lem1406 t h1 h2 (@lem1397 t h2)). Qed.
Lemma lem1408 (t : Prop) (h1 : t = False) : t -> False.
Proof. exact (fun h0 : t => @lem1407 t h0 h1). Qed.
Lemma lem1409 (t : Prop) : (t -> False) = (~ t).
Proof. exact (@lem69 t). Qed.
Lemma lem1410 (t : Prop) (h1 : t = False) : ~ t.
Proof. exact (EQ_MP (@lem1409 t) (@lem1408 t h1)). Qed.
Lemma lem1411 (t : Prop) : term30 t.
Proof. exact (fun h0 : t = False => @lem1410 t h0). Qed.
Lemma lem1412 (t : Prop) (h1 : ~ t) : ~ t.
Proof. exact (h1). Qed.
Lemma lem1413 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1414 (t : Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1415 (t : Prop) : (~ t) = (term21 t).
Proof. exact (MK_COMB (@lem56) (@lem1414 t)). Qed.
Lemma lem1416 (t : Prop) : (term21 t) = (t -> False).
Proof. exact (eq_refl (term21 t)). Qed.
Lemma lem1417 (t : Prop) : (term22 t) = (term22 t).
Proof. exact (eq_refl (term22 t)). Qed.
Lemma lem1418 (t : Prop) : ((~ t) = (term21 t)) = ((~ t) = (t -> False)).
Proof. exact (MK_COMB (@lem1417 t) (@lem1416 t)). Qed.
Lemma lem1419 (t : Prop) : (~ t) = (t -> False).
Proof. exact (EQ_MP (@lem1418 t) (@lem1415 t)). Qed.
Lemma lem1420 (t : Prop) (h1 : ~ t) : t -> False.
Proof. exact (EQ_MP (@lem1419 t) (@lem1412 t h1)). Qed.
Lemma lem1421 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1422 (t : Prop) (h1 : t) (h2 : ~ t) : False.
Proof. exact (@lem1420 t h2 (@lem1421 t h1)). Qed.
Lemma lem1423 (t : Prop) (h1 : t) (h2 : ~ t) : t = False.
Proof. exact (prop_ext (fun h3 : t => @lem1422 t h1 h2) (fun h3 : False => @lem1413 t h1)). Qed.
Lemma lem1424 (t : Prop) (h1 : t) (h2 : ~ t) : False.
Proof. exact (EQ_MP (@lem1423 t h1 h2) (@lem1413 t h1)). Qed.
Lemma lem1425 (t : Prop) (h1 : ~ t) : t -> False.
Proof. exact (fun h0 : t => @lem1424 t h0 h1). Qed.
Lemma lem1426 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1427 (t : Prop) (h1 : False) : t.
Proof. exact (@lem98 t h1). Qed.
Lemma lem1428 (t : Prop) (h1 : False) : False = t.
Proof. exact (prop_ext (fun h2 : False => @lem1427 t h1) (fun h2 : t => @lem1426 h1)). Qed.
Lemma lem1429 (t : Prop) (h1 : False) : t.
Proof. exact (EQ_MP (@lem1428 t h1) (@lem1426 h1)). Qed.
Lemma lem1430 (t : Prop) : False -> t.
Proof. exact (fun h0 : False => @lem1429 t h0). Qed.
Lemma lem1431 (t : Prop) (h1 : ~ t) : term31 t.
Proof. exact (conj (@lem1425 t h1) (@lem1430 t)). Qed.
Lemma lem1432 (t : Prop) : (term31 t) = (t = False).
Proof. exact (@lem32 t False). Qed.
Lemma lem1433 (t : Prop) (h1 : ~ t) : t = False.
Proof. exact (EQ_MP (@lem1432 t) (@lem1431 t h1)). Qed.
Lemma lem1434 (t : Prop) : term32 t.
Proof. exact (fun h0 : ~ t => @lem1433 t h0). Qed.
Lemma lem1435 (t : Prop) : term33 t.
Proof. exact (conj (@lem1411 t) (@lem1434 t)). Qed.
Lemma lem1436 (t : Prop) : (term33 t) = ((t = False) = (~ t)).
Proof. exact (@lem32 (t = False) (~ t)). Qed.
Lemma lem1437 (t : Prop) : (t = False) = (~ t).
Proof. exact (EQ_MP (@lem1436 t) (@lem1435 t)). Qed.
Lemma lem1438 (t : Prop) : term34 t.
Proof. exact (conj (@lem1388 t) (@lem1437 t)). Qed.
Lemma lem1439 (t : Prop) : term35 t.
Proof. exact (conj (@lem1333 t) (@lem1438 t)). Qed.
Lemma lem1440 (t : Prop) : term36 t.
Proof. exact (conj (@lem1296 t) (@lem1439 t)). Qed.
Lemma lem1445 : term37.
Proof. exact (fun t : Prop => @lem1440 t). Qed.
