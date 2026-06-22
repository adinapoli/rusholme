module Main where

-- Tuples of arity 8..62 and functions with >8 arguments,
-- exercising the lifted backend 8-argument cap (#865, epic #845).

sum8 :: (Int,Int,Int,Int,Int,Int,Int,Int) -> Int
sum8 (v0,v1,v2,v3,v4,v5,v6,v7) = v0+v1+v2+v3+v4+v5+v6+v7

add9 :: Int->Int->Int->Int->Int->Int->Int->Int->Int->Int
add9 a0 a1 a2 a3 a4 a5 a6 a7 a8 = a0+a1+a2+a3+a4+a5+a6+a7+a8

sum62 :: (Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int) -> Int
sum62 (v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61) = v0+v1+v2+v3+v4+v5+v6+v7+v8+v9+v10+v11+v12+v13+v14+v15+v16+v17+v18+v19+v20+v21+v22+v23+v24+v25+v26+v27+v28+v29+v30+v31+v32+v33+v34+v35+v36+v37+v38+v39+v40+v41+v42+v43+v44+v45+v46+v47+v48+v49+v50+v51+v52+v53+v54+v55+v56+v57+v58+v59+v60+v61

mk62 :: (Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int,Int)
mk62 = (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62)

caseSum :: Int
caseSum = case mk62 of
  (v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61) -> v0+v1+v2+v3+v4+v5+v6+v7+v8+v9+v10+v11+v12+v13+v14+v15+v16+v17+v18+v19+v20+v21+v22+v23+v24+v25+v26+v27+v28+v29+v30+v31+v32+v33+v34+v35+v36+v37+v38+v39+v40+v41+v42+v43+v44+v45+v46+v47+v48+v49+v50+v51+v52+v53+v54+v55+v56+v57+v58+v59+v60+v61

main :: IO ()
main = do
  print (sum8 (1,2,3,4,5,6,7,8))
  print (add9 1 2 3 4 5 6 7 8 9)
  print (sum62 mk62)
  print caseSum
