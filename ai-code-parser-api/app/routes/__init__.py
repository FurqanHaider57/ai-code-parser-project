from flask import Blueprint

# Initialize the routes blueprint
routes_bp = Blueprint('routes', __name__)

from .debugging import *
from .nlp import *
from .formal import *