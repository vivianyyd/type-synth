data X = Y | Z
         deriving (Eq, Show)

type R = [X]
type W = [R]

example = map (\x -> take x (cycle [Y, Z])) [0..]

main = undefined
