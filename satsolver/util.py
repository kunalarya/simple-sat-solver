class Result(object):
    def __init__(self):
        self.success = False
        self.result = None
        self.reason = ''


class Failure(Result):
    def __init__(self, reason='', result=None):
        self.result = result
        self.reason = reason
        self.success = False

    def __repr__(self):
        return '<Failure reason="{}">'.format(self.reason[:20])


class Success(Result):
    def __init__(self, result=None):
        self.result = result
        self.reason = ''
        self.success = True

    def __repr__(self):
        return '<Success>'
