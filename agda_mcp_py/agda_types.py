from pydantic import BaseModel
from typing import Optional


class AgdaLoad(BaseModel):
    file: str


class AgdaGetGoals(BaseModel):
    pass


class AgdaGetGoalType(BaseModel):
    goalId: int


class AgdaGetContext(BaseModel):
    goalId: int


class AgdaGive(BaseModel):
    goalId: int
    expression: str


class AgdaRefine(BaseModel):
    goalId: int
    expression: str


class AgdaCaseSplit(BaseModel):
    goalId: int
    variable: str


class AgdaCompute(BaseModel):
    goalId: int
    expression: str


class AgdaInferType(BaseModel):
    goalId: int
    expression: str


class AgdaIntro(BaseModel):
    goalId: int


class AgdaWhyInScope(BaseModel):
    name: str


class AgdaAuto(BaseModel):
    goalId: int


class AgdaAutoAll(BaseModel):
    pass
