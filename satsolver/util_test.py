from satsolver.util import Result, Failure, Success


def test_result():
    res = Result()
    assert not res.success
    assert res.result is None


def test_success_defaults():
    suc = Success()
    assert suc.success
    assert suc.result is None


def test_success_with_result():
    suc = Success(result=1234)
    assert suc.success
    assert suc.result == 1234


def test_failure_defaults():
    fai = Failure()
    assert not fai.success
    assert fai.reason == ''


def test_failure_with_reason():
    fai = Failure('within reason')
    assert not fai.success
    assert fai.reason == 'within reason'
