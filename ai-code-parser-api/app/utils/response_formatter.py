def format_response(data, message="Success", status_code=200):
    return {
        "status": status_code,
        "message": message,
        "data": data
    }

def format_error(message="An error occurred", status_code=400):
    return {
        "status": status_code,
        "message": message,
        "data": None
    }